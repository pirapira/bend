# RFC: Prop and `!`, an exponential for propositions

Status: proposal. Nothing in this document is implemented.

## Summary

Add a kind `Prop` of propositions and a type former `!P`, read "of course
P", that promotes a proposition to `Data`. A proof of a proposition is
checked as evidence, meaning it must terminate and may not be dead code, but
it carries no usage discipline: a proof may be used any number of times,
because the compiler erases every proof to the token `Quant`, exactly as it
erases equations and `{==}` today. So `!` costs nothing at runtime, copies
nothing and allocates nothing, and the affine discipline on `Type` and
`Data`, which is what keeps the runtime free of a garbage collector, is
untouched.

The payoff is that intuitionistic type theory as Rocq and Lean write it
embeds into Bend by Girard's translation, `A -> B` becoming `!A -> B`: a
proof of `P -> Q -> P` uses its first hypothesis under a second one, a
proof by induction reuses its hypothesis in two branches, and a proof of
`Not(Not(Not A)) -> Not A` applies a negation twice. None of these type in
Bend today, because their hypotheses are function-valued and function types
are never `Data`.

The price is two rules that Bend does not have today, and one proof it
does not have. Datatypes of kind `Prop` must be strictly positive, and
`Type` must become a hierarchy `Type(0) : Type(1) : ...`, since contraction
inside `Prop` reopens Russell's and Girard's paradoxes, which the usage wall
closed. And `bend.lean`'s consistency proof, which is a proof about the
wall, does not cover the `Prop` fragment; a new one is needed. The second
half of this document is about that.

## Why the wall does not carry over

`bend.lean` states the design in one line: a `Many` binder forms only at a
`Data` type, and no function type is `Data`. So every self-replicating term
(omega, Curry, Hurkens) contracts a live function-valued binding and does
not type. `bend2/russell.lean` (branch `russell`) mechanizes this on the
Russell set:

    type R is Type:
      In{f: R -> Empty}

    def omega(x: R) -> Empty:
      match x:
        case In{f}:
          f(x)

`omega` is rejected because `x` is used twice under a `Lone` binder, and
`+x` is rejected because `R` holds a function.

Now let `R` be a proposition and let `!` be unrestricted:

    type R is Prop:
      In{f: !R -> Empty}

    def omega(+x: !R) -> Empty:
      match x:
        case In{f}:
          f(x)

    def main() -> Empty:
      omega(!In{omega})

Every step is licensed. `x : !R` is `Data`, so `+x` forms; `f(x)` is the
second use it licenses; `In{omega}` is closed, so it promotes. `Empty` is
inhabited. Nothing about the runtime went wrong: `main` is erased to a
token. The theory is simply inconsistent, and what made it so is that `R`
mentions itself to the left of an arrow. `Prop` needs positivity because
`Prop` has contraction, and the wall was only ever a substitute for
positivity on the fragment that lacks contraction.

The same happens one level up. `bend2/universe.lean` (branch `type-in-type`)
shows Hurkens' universe `(-X: Type) -> ((P(P(X)) -> X) -> P(P(X))` is a
`Type` today, harmlessly, because Hurkens' proof term contracts a function.
In `Prop` with `Prop : Type : Type` the same term types. Rocq's
`-type-in-type` is inconsistent for exactly this reason. So `Prop`
impredicative needs `Type` predicative: a hierarchy.

## The design

### Kinds

Today a kind is `Kind(q)` for a quantity `q`, with `Type = Kind(&1)` and
`Data = Kind(&2)`. Add

    Prop                 the kind of propositions
    Type(i)              the hierarchy; Type = Type(0); Type(i) : Type(i+1)
    Prop : Type(0)
    Data  fits Type(i)   unchanged: Data fits Type
    Prop  fits Type(i)   a proposition is a type, so it may be quantified over

`Prop` is impredicative: `for P: Prop, P -> P` is a `Prop`. `Type(i)` is
predicative in the usual way: an arrow whose domain is `Type(i)` lives in
`Type(i+1)` at least. `Kind(q)` stays as the kind algebra for `Type` and
`Data`; `Prop` is a fourth quantity value only in the sense that it sits
under all of them in `KLe`.

`Empty` moves to `Prop`. Today it is `Data` with no constructor; as a
`Prop` it is `False`, and ex falso (`check-efq`) from a proof of it into any
goal is unchanged, since check-efq already accepts any live emptied binding.
`Unit` stays `Data`; `True` is a new `Prop` with one constructor.

### Proof mode

`Check` today has two demands, `None` (dead) and `Lone` (live). Add a third:

    Proof     evidence: must terminate and may not promote dead code,
              but every binder is Many and no use is counted

A term is checked at demand `Proof` when its goal is a `Prop`. The rules
that differ from `Lone`:

    infer-var    charges nothing: π = {}
    check-lam    the binder's quantity is ignored; π[0] <= q' is not tested
    check-let    likewise
    infer-ref    a self-reference must still descend (lhs_descend), and a
                 reference must still point backward: a proof is not dead
    check-any    conversion unchanged

Everything else is the `Lone` rule. In particular a proof may `match` on a
`Data` or `Type` value it is given (case analysis on a number), and it may
call a filled `Type`-valued def (a decision procedure), because those are
live and terminate. What it may not do is be *used* by live code except
through ex falso, `!`, or an equation: a proof is not a value.

### `!P`

    Γ ⊢ P : Prop
    -------------------------- form
    Γ ⊢ !P : Data

    Γ ⊢ p : P    at demand Proof
    -------------------------- promotion; live at any demand
    Γ ⊢ !p : !P ~ {}

    Γ ⊢ e : !P ~ πe    Γ, +x : P ⊢ f : T ~ π     (x usable in proofs only)
    ----------------------------------------- dereliction, by a let
    Γ ⊢ !x = e; f : T ~ πe + tail π

`!P` is `Data`, so it enters a `+` binder, a field of a `Data` type and a
`let +x`. The compiler represents every `!p` as the token, so a `+` binder
over `!P` copies nothing: this is the reason `!` is free. Promotion
measures `{}`: a proof consumes no live resource, since it uses none. There
is no rule for promoting a term that consumes live variables, because a
proof cannot consume one; a proof may mention a live variable only as a
subject (`{x == y : T}`), which is dead code today and stays dead.

`for y: B where P(y)` in a law today makes `y` the pair `(y, proof)`. With
`!` it is `Sigma<B, y => !P(y)>`, and the proof half is a token.

### Girard's translation

An intuitionistic judgment `x1 : A1, ..., xn : An ⊢ t : B` over
propositions maps to Bend as

    for +x1: !A1, ..., for +xn: !An,  B          at demand Proof

with `A -> B` sent to `!A -> B` and every hypothesis applied through
dereliction. Since Proof mode ignores quantities, the `!` on hypotheses is
inferable: a `Prop`-kinded law may write `A -> B` and mean `!A -> B`. The
surface syntax can hide `!` inside `Prop` entirely and require it only at
the boundary, where a proof is stored in `Data` or passed to live code. The
RFC proposes doing exactly that: `!` is written by the user only at the
boundary, and `bend base` prints it there.

Proofs by induction reuse the hypothesis freely:

    law le_trans:
      for x: Nat
      for y: Nat
      for z: Nat
      Le(x, y) -> Le(y, z) -> Le(x, z)

    def le_trans(x, y, z):
      match x: ...     # each arm may use both hypotheses, and le_trans(p, ..)
                       # twice, as long as every self-call descends

None of this needs `+` on the hypotheses, since the goal is a `Prop`.

### Positivity

A datatype `type D is Prop:` must be strictly positive: `D` and any
parameter of kind `Prop` occur in a field type only to the right of arrows,
and never as an argument of another family's parameter unless that family
is itself known positive in that parameter. `Type` and `Data` datatypes are
unchanged: the wall still guards them, and a negative `Type` datatype is
still admitted.

A `Prop` datatype may have fields of kind `Type` or `Data` (a witness), and
a `Data` datatype may have fields `!P` (a stored proof) but not `P`.
Elimination out of `Prop` into `Type` or `Data` is limited to ex falso and
to `Prop` datatypes with at most one constructor whose fields are all
`Prop` (singleton elimination, as in Rocq), because the proof is erased
and nothing is there to branch on at runtime.

### What changes, per file

    bend2/bend.ts    Prop and Type(i) in Kind; the Proof demand in Check;
                     the !, promotion and dereliction rules; the positivity
                     walk in adt_valid; the elimination restriction in
                     check-mat; level inference for Type(i)
    bend2/comp.ts    nothing: a Prop-typed term never reaches the emitters,
                     since it elaborates to the token. This is the claim
                     that makes the RFC cheap, and gates/test.ts must check
                     it: every test's compiled output is byte-identical
                     before and after on programs that carry proofs
    bend2/base.bend  Empty becomes Prop; True; Not; And, Or, Exists as Prop
                     datatypes; the pair in `where` carries !P
    guide/GUIDE.md   the Laws and Proofs section: hypotheses reusable;
                     the boundary rule for !
    bend2/bend.lean  see below
    tests/prop/      the omega program above (must fail: positivity);
                     Hurkens in Prop (must fail: level); le_trans;
                     triple negation; a stored proof in a Data field

## Metatheory

`bend.lean` proves five claims for the live fragment, and the fifth,
consistency, rests on normalization, whose argument is the wall: every
live binder is used at most once, so weak reduction of a closed live term
never duplicates a redex, and every live self-call descends. Proof mode
removes the first half of that for the `Prop` fragment. A proof that copies
its hypothesis twice does duplicate a redex, and the measure that
normalization runs on is broken.

What replaces it is the standard argument for CIC's `Prop`: strong
normalization of an impredicative, strictly positive fragment, by
reducibility candidates. That proof is known and is not small. In
`bend.lean` terms the plan is:

1. `Check` gets the demand `Proof`, the two new rules and the kind `Prop`
   and `Typ (i)` in §1 and §9. The existing lemmas about `None` and `Lone`
   are unaffected by construction, since a `Proof` premise never feeds a
   `Lone` conclusion except through promotion, which measures `{}`.

2. Positivity is a predicate `AdtD.Positive` in §10, and `Book.Ok` demands
   it of every `Prop` family.

3. Normalization for `Proof` demand is a new part, §P, by candidates over
   the closed `Prop` fragment, with the datatypes handled by their
   positivity. Its consistency corollary is the same sentence as today's:
   no closed term at demand `Lone` or `Proof` inhabits `Empty`.

4. The five claims are restated for `Lone` and `Proof` and the old proofs
   are reused for `Lone`.

Step 3 is the risk. It is a proof of roughly the size of §K through §Z
today, and until it exists the RFC's consistency is an argument by analogy
with CIC, not a theorem. `russell.lean` and `universe.lean` should be kept
as regression tests of the two paradoxes: `omega` in `Prop` must fail
positivity, and Hurkens in `Prop` must fail the level check.

## Relation to the `bang` branch

The fork's `bang` branch adds `!` as a fourth binder quantity next to `-`,
plain and `+`: a `!` parameter or `!` let is reusable at any kind, and the
call pays by passing a closed term, a recipe the callee re-runs per use.
`!` never marks a field, a datatype parameter or a function type, so no
datatype holds a recipe and the wall stands; its commit message works
through the same `!R -> Empty` omega as above and rejects each shape that
admits it. `bend2/bang.lean` there states the rules and proves the
extension conservative on the base fragment, with consistency stated and
not proved.

The two designs answer different questions, and they compose:

| | `bang` (recipes) | this RFC (`Prop`) |
|---|---|---|
| where `!` lives | def and law parameters, lets, any kind | propositions only |
| what may be promoted | a closed term | any proof, hypotheses included |
| runtime | re-runs the recipe per use | nothing: erased |
| wall | stands; no positivity, no hierarchy | replaced in `Prop` by positivity and a hierarchy |
| metatheory | conservative extension; consistency open | new normalization proof needed |
| Girard's translation | only for closed hypotheses | full |

The last row is the reason this RFC exists. Girard's promotion rule allows
a term to be promoted when every free variable it mentions is itself
under `!`. A recipe must be closed, so a proof may not promote a
hypothesis it was given, and the translation of an intuitionistic proof
that uses a hypothesis twice inside a lambda has no image. Inside `Prop`
that restriction has no purpose, since nothing is ever run; so `Prop` is
where the restriction can be dropped, and `Type` is where `bang`'s recipe
discipline is the right one because there something does run.

If both land, the surface has one `!`: on a `Type` or `Data` binder it is
`bang`'s recipe, on a `Prop` binder it is free. The checker distinguishes
them by the kind of the domain, which it already computes.

## Non-goals

- No `!` on `Type` or `Data`. `!(A -> B)` for a live function would copy a
  closure, and the runtime is affine precisely so that it never has to.
  This is the one line the RFC draws, and it is the reason `!` is safe.
- No classical axioms. An unfilled law stays a dead claim that live code,
  and now proofs, cannot use. Excluded middle as an axiom would be a
  separate RFC; nothing here needs it, and Girard's translation is of
  intuitionistic logic.
- No tactics. Proofs are still defs.

## Open questions

- Should `Prop` be impredicative? Rocq and Lean say yes and it is what
  the Girard translation of their logics needs. Predicative `Prop` would
  make step 3 above a much smaller proof (no candidates) at the cost of
  `for P: Prop, P -> P` living in `Type(0)` rather than `Prop`.
- Level inference for `Type(i)`: explicit annotations, or floating levels
  as Rocq does? The former is simpler and matches Bend's taste for terse,
  explicit terms; the latter is what makes a hierarchy bearable.
- Does `bend PROOF.bend` still print "All terms check." for a proof that
  uses no `!` at all? It should: the boundary rule means most proof files
  never mention it.
