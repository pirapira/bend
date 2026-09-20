-- ============================================================================
-- RUSSELL — the Russell set in bend-core, admitted as a type and refuted as
-- a proof
-- ============================================================================
--
-- bend.lean's headline: a calculus with Type : Type and negative recursive
-- types, kept consistent by a usage wall rather than by a universe
-- hierarchy or a positivity check. This file exercises that headline on the
-- oldest paradox there is. Russell's set, {x | x ∉ x}, is in type theory a
-- datatype R whose one constructor holds a refutation of R itself:
--
--     type R is Type:
--       In{f: R -> Empty}
--
-- and the paradox is omega, the function that opens an R and applies the
-- refutation inside it to the R it came from:
--
--     def omega(x: R) -> Empty:      def main() -> Empty:
--       match x:                       omega(In{omega})
--         case In{f}:
--           f(x)
--
-- With contraction this is a closed proof of Empty. Here it is not, and the
-- reason is exactly where the wall says: omega's body uses its argument x
-- twice, once as the scrutinee and once as the argument of f, but x's
-- binder is Lone and R, a function-bearing type, can never be Data, so no
-- binder over it may be Many.
--
-- The file proves three things about a two-family book, Empty (index 0)
-- and R (index 1):
--
--   (1) book_ok:         the book is Book.Ok. bend-core admits the Russell
--                        set as a type, negative occurrence and all, with no
--                        positivity check to fail.
--   (2) omega_untyped:   omega's body does not check LIVE at its declared
--                        type, in this book or any closed extension of it,
--                        under any equation. The proof walks the inversion
--                        lemmas of bend.lean's §E down to the two uses of x
--                        and meets the Lone bound of check-lam.
--   (3) russell_refuted: no closed live term of type Empty exists in the
--                        book, so in particular omega(In{omega}) is not one.
--                        This is consistency_holds, instantiated.
--
-- (2) is the local reason and (3) the global consequence: even if omega
-- were smuggled in some other way, the five claims already rule out what
-- it would prove. The file lives beside bend.lean, imports it as a module
-- and adds no axiom to the five claims' three.
--
-- To check:  lean -o bend.olean bend.lean; LEAN_PATH=. lean russell.lean

import bend

namespace BendCore
namespace Russell

-- ----------------------------------------------------------------------------
-- The book
-- ----------------------------------------------------------------------------

-- Empty: a family of kind Type with no constructor
def emptyD : AdtD := ⟨0, .Typ (.Qua .Lone), []⟩

-- R -> Empty: the type of In's one field. A refutation is a live function,
-- so its binder is Lone
def rField : Term := .All .Lone (.Ref 1) (.Ref 0)

-- In{f: R -> Empty}: one Lone field, tipped at R. (R has no parameter, so
-- the telescope is the field binder alone)
def inD : CtrD := ⟨1, .All .Lone rField (.Adt 1 [])⟩

-- R: a family of kind Type with the one constructor In. The field mentions
-- R to the left of an arrow: the datatype is negative
def rD : AdtD := ⟨0, .Typ (.Qua .Lone), [inD]⟩

-- Empty at 0, R at 1
def book : Book := [.adt emptyD, .adt rD]

-- ----------------------------------------------------------------------------
-- (1) the book is Ok: Bend admits the Russell set
-- ----------------------------------------------------------------------------

-- Type : Type, checked dead (infer-typ over infer-qua)
theorem typ_ok (β : Book) (L : LHS) (Γ : Ctx) :
    Check β (Pol.std β) L [] .None Γ (.Typ (.Qua .Lone)) (.Typ (.Qua .Lone)) Uses.zero .Qnt :=
  Check.typ Check.qua

-- R -> Empty : Type, checked dead in any book that holds Empty at 0 and R
-- at 1 as nullary families (infer-all over two infer-ref (adt))
theorem rField_ok (β : Book) (hE : Book.adt β 0 = some emptyD) (hR : Book.adt β 1 = some rD)
    (L : LHS) (Γ : Ctx) :
    ∃ π, Check β (Pol.std β) L [] .None Γ rField (.Typ (.Qua .Lone)) π .Qnt :=
  ⟨Uses.zero, Check.all (Check.refA hR rfl) (Check.refA hE rfl)⟩

theorem book_ok : Book.Ok book := by
  intro k t hk
  match k, hk with
  | 0, hk =>
    cases hk
    refine ⟨⟨Uses.zero, typ_ok _ _ _⟩, .Qua .Lone, Red.refl, ?_⟩
    intro c C hc
    cases c <;> simp [emptyD, AdtD.ctr, AdtD.ctr.go] at hc
  | 1, hk =>
    cases hk
    refine ⟨⟨Uses.zero, typ_ok _ _ _⟩, .Qua .Lone, Red.refl, ?_⟩
    intro c C hc
    match c, hc with
    | 0, hc =>
      cases hc
      refine ⟨⟨.Lone, rField, .Adt 1 [], rfl, rfl⟩, ?_⟩
      exact ⟨rField_ok book rfl rfl _ _, trivial⟩
    | c + 1, hc => cases c <;> simp [rD, AdtD.ctr, AdtD.ctr.go] at hc
  | k + 2, hk => cases k <;> simp [book, Book.tld] at hk

-- and R and In have the types the surface program declares: R : Type and
-- In : (R -> Empty) -> R
theorem r_typed (L : LHS) (sp : List Term) (q : Quant) (Γ : Ctx) :
    Check book (Pol.std book) L sp q Γ (.Ref 1) (.Typ (.Qua .Lone)) Uses.zero (Term.era q (.Ref 1)) :=
  Check.refA (A := rD) rfl rfl

theorem in_typed (L : LHS) (sp : List Term) (q : Quant) (Γ : Ctx) :
    Check book (Pol.std book) L sp q Γ (.Ctr 1 0) (.All .Lone rField (.Adt 1 []))
      Uses.zero (Term.era q (.Ctr 1 0)) :=
  Check.ctr (A := rD) (C := inD) (r := []) rfl rfl (by simp)

-- ----------------------------------------------------------------------------
-- (2) omega does not check live: the wall
-- ----------------------------------------------------------------------------

-- the In arm: f => f(x), with f at 0 and x, the scrutinee, at 1
def omegaArm : Term := .Lam (.App (.Var 0) (.Var 1))

-- x => match x { In f => f(x) }: the match peels In and has no other
-- constructor to refute
def omegaBody : Term := .Lam (.App (.Mat 1 0 omegaArm .Efq) (.Var 0))

-- R -> Empty, omega's declared type
def omegaTy : Term := rField

-- a context of binders without values expands nothing
theorem δ_lam1 (q : Quant) (A : Term) (d : Nat) (t : Term) :
    Ctx.δ [⟨q, A, none⟩] d t = t :=
  Ctx.δ_rigid _ (by intro b hb; simp at hb; subst hb; rfl) d t

theorem δ_lam2 (q q' : Quant) (A A' : Term) (d : Nat) (t : Term) :
    Ctx.δ [⟨q, A, none⟩, ⟨q', A', none⟩] d t = t :=
  Ctx.δ_rigid _ (by intro b hb; simp at hb; rcases hb with rfl | rfl <;> rfl) d t

-- infer-app at a head that is no lambda: the one-beta case is out
theorem app_inv' (hΦ : Pol.Pre Φ) (hnl : ∀ g, f ≠ .Lam g)
    (h : Check β Φ L sp q Γ (.App f x) T π u) :
    ∃ q' A B πf uf πx ux, Check β Φ L (x :: sp) q Γ f (.All q' A B) πf uf ∧
      Check β Φ L [] (Quant.dem q' q) Γ x A πx ux ∧
      Φ.conv (Ctx.δ Γ 0 (Term.subst 0 x B)) (Ctx.δ Γ 0 T) ∧
      π = Uses.add πf πx ∧ u = Term.era q (.App uf ux) := by
  rcases Check.app_inv hΦ h with h' | ⟨g, _, hg, _⟩
  · exact h'
  · exact absurd hg (hnl g)

-- the wall, stated for any closed book that holds R at 1: omega's body has
-- no live derivation at its declared type, under any equation, any pending
-- spine, measure and erasure
theorem omega_untyped (β : Book) (hβ : Book.Closed β) (hR : Book.adt β 1 = some rD)
    (L : LHS) (sp : List Term) (π : Uses) (u : Term) :
    ¬ Check β (Pol.std β) L sp .Lone [] omegaBody omegaTy π u := by
  intro h
  have hΦ : Pol.Pre (Pol.std β) := Pol.std_pre hβ
  -- check-lam: the binder x is q', and q' = Lone since the type is R -> Empty
  obtain ⟨q', A, B, _, π', uf, _, hf, hle, hcv, _, _⟩ := Check.lam_inv hΦ h
  simp only [Pol.std, Ctx.δ_nil] at hcv
  obtain ⟨rfl, _, _⟩ := Le.all_inv hβ hcv Red.refl Red.refl
  -- so x occurs at most once in the body's erasure
  have hocc : Term.occ 0 uf ≤ 1 := Check.occ_le hf hle
  -- infer-app: the match applied to x. x is checked at the demand of the
  -- match's binder
  obtain ⟨q1, A1, B1, πm, um, πx, ux, hm, hx, _, _, rfl⟩ :=
    app_inv' hΦ (fun _ h => Term.noConfusion h) hf
  -- check-mat: the binder is live, since the region is
  obtain ⟨A', C, r, ps, q2, telF, B2, G, πh, uh, πm', um', hA', hC, _, hps, hlive, hins,
    hgoal, hh, _, hcm, _, rfl⟩ := Check.mat_inv hΦ hm
  simp only [Pol.std, δ_lam1] at hcm
  obtain ⟨rfl, _, _⟩ := Le.all_inv hβ hcm Red.refl Red.refl
  have hq2 : q2 ≠ .None := hlive (by decide)
  -- so x, the scrutinee, is live: its erasure is x itself
  rw [Quant.dem_live hq2] at hx
  obtain ⟨_, _, _, _, rfl⟩ := Check.var_inv hΦ hx
  -- the arm handles In's one field, of type R -> Empty
  rw [hR] at hA'; cases hA'
  obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hps
  simp only [rD, inD, AdtD.ctr, AdtD.ctr.go, Option.some.injEq] at hC; subst hC
  cases hins
  change MatGoal _ _ _ _ (.All .Lone rField (.Adt 1 [])) _ at hgoal
  rcases hgoal with _ | hg'
  cases hg'
  -- check-lam for the arm: f's binder converts to R -> Empty
  obtain ⟨q3, A3, B3, _, π3, u3, _, hb, _, hcv3, _, rfl⟩ := Check.lam_inv hΦ hh
  simp only [Pol.std, δ_lam1] at hcv3
  obtain ⟨_, hA3, _⟩ := Le.all_inv hβ hcv3 Red.refl Red.refl
  -- infer-app for f(x): f's type is R -> Empty up to conversion, so x is
  -- checked live and its erasure is x itself
  obtain ⟨q4, A4, B4, _, u4, _, u5, hf4, hx4, _, _, rfl⟩ :=
    app_inv' hΦ (fun _ h => Term.noConfusion h) hb
  obtain ⟨b, hget, hcv4, _, rfl⟩ := Check.var_inv hΦ hf4
  simp only [Ctx.get, Bind.shift, Option.some.injEq] at hget
  subst hget
  simp only [Pol.std, δ_lam2] at hcv4
  have hA3' : Le β rField (Term.shift 0 A3) := by
    have := Le.shift hβ hA3 0
    rwa [show Term.shift 0 rField = rField from rfl] at this
  obtain ⟨rfl, _, _⟩ := Le.all_inv hβ (Le.trans hβ hA3' hcv4) Red.refl Red.refl
  rw [Quant.dem_live (by decide)] at hx4
  obtain ⟨_, _, _, _, rfl⟩ := Check.var_inv hΦ hx4
  -- x occurs twice in the erasure: contradiction
  simp [Term.occ, Term.era] at hocc

-- in particular, no Ok book extending ours holds omega as a definition, at
-- any index and with any column quantities
theorem omega_not_def (γ : Book) (hok : Book.Ok (book ++ γ)) (k n : Nat) (qs : List Quant) :
    Book.defn (book ++ γ) k ≠ some ⟨n, qs, omegaTy, omegaBody⟩ := by
  intro hk
  obtain ⟨_, _, _, _, π, u, h⟩ := Book.Ok.defn hok hk
  exact omega_untyped _ hok.closed rfl _ _ π u h

-- ----------------------------------------------------------------------------
-- (3) the paradox proves nothing: consistency, instantiated
-- ----------------------------------------------------------------------------

-- In{omega} and omega(In{omega})
def inOmega : Term := .App (.Ctr 1 0) omegaBody
def russell : Term := .App omegaBody inOmega

-- Empty is empty
theorem empty_empty : Book.empty book 0 [] :=
  ⟨emptyD, rfl, fun c hc => absurd hc (by simp [emptyD])⟩

-- no closed live term inhabits Empty in the book
theorem no_proof_of_empty (t : Term) (π : Uses) (u : Term) :
    ¬ Check book (Pol.std book) (LHS.void book) [] .Lone [] t (.Adt 0 []) π u :=
  consistency_holds book 0 [] [] t π u book_ok empty_empty

-- so omega(In{omega}) is not one
theorem russell_refuted (π : Uses) (u : Term) :
    ¬ Check book (Pol.std book) (LHS.void book) [] .Lone [] russell (.Adt 0 []) π u :=
  no_proof_of_empty russell π u

end Russell
end BendCore

#print axioms BendCore.Russell.book_ok
#print axioms BendCore.Russell.omega_untyped
#print axioms BendCore.Russell.omega_not_def
#print axioms BendCore.Russell.russell_refuted
