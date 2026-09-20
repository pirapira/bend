-- ============================================================================
-- UNIVERSE — Type : Type in bend-core, one universe and what it does not buy
-- ============================================================================
--
-- Bend has one universe. Type is Kind(&1), Data is Kind(&2), and every kind
-- is a term of type Type, Type itself included: the term on the two sides of
-- Type : Type is the same term, Typ (Qua Lone), with no level to climb.
-- Predicative theories forbid this because with a universe hierarchy
-- Girard's paradox (Hurkens' form) is a closed proof of False in Type : Type
-- with unrestricted quantification. bend.lean's headline is that the usage
-- wall, not a hierarchy, is what rules that out.
--
-- This file shows the two halves on the model:
--
--   (1) type_in_type, kind_in_type, one_type:
--         Type : Type holds, live, in every book, under every policy; every
--         Kind(g) lands in Type; and a kind has no other type up to
--         conversion: there is nothing above Type.
--   (2) id_ok, id_at_type:
--         a polymorphic identity id : (-X: Type) -> X -> X, filled, is
--         applied to Type itself: id(Type, Type) : Type. A hierarchy would
--         put Type one level above X's range; here they are the same Type.
--   (3) hurkensU_ok:
--         Hurkens' universe U = (-X: Type) -> ((P(P(X)) -> X) -> P(P(X)),
--         with P(X) = X -> Type, is a Type. This is the formation the
--         hierarchy exists to forbid, and the first line of Girard's
--         paradox. bend-core forms it without complaint.
--   (4) no_proof_of_false:
--         the paradox's conclusion, the impredicative False (-X: Type) -> X,
--         has no closed live inhabitant, in the book with an empty family.
--         This is consistency_holds, applied through one infer-app.
--
-- So the model admits the universe the paradox needs and still refutes what
-- the paradox proves. Hurkens' term itself is not written out here: it is
-- rejected for the same reason as omega in russell.lean, a live
-- function-valued binding used twice, and (4) says that however it is
-- written, it is not a proof.
--
-- To check:  lean -o bend.olean bend.lean; LEAN_PATH=. lean universe.lean

import bend

namespace BendCore
namespace Universe

-- ----------------------------------------------------------------------------
-- (1) one universe
-- ----------------------------------------------------------------------------

-- Type, the term; Kind(&1)
def type : Term := .Typ (.Qua .Lone)

-- Type : Type, the same term on both sides, at any demand, in any book,
-- under any policy, equation, spine and context (infer-typ over infer-qua)
theorem type_in_type (β : Book) (Φ : Pol) (L : LHS) (sp : List Term) (q : Quant) (Γ : Ctx) :
    Check β Φ L sp q Γ type type Uses.zero (Term.era q (.Typ .Qnt)) :=
  Check.typ Check.qua

-- every kind Kind(g) whose quantity checks is in Type: Data too
theorem kind_in_type (β : Book) (Φ : Pol) (L : LHS) (sp : List Term) (q : Quant) (Γ : Ctx)
    (g : Term) (πg : Uses) (hg : Check β Φ L [] .None Γ g .Qnt πg .Qnt) :
    Check β Φ L sp q Γ (.Typ g) type Uses.zero (Term.era q (.Typ .Qnt)) :=
  Check.typ hg

theorem data_in_type (β : Book) (Φ : Pol) (L : LHS) (sp : List Term) (q : Quant) (Γ : Ctx) :
    Check β Φ L sp q Γ (.Typ (.Qua .Many)) type Uses.zero (Term.era q (.Typ .Qnt)) :=
  Check.typ Check.qua

-- and nothing above it: whatever type a kind is checked at converts to
-- Type. A hierarchy would give Type : Type₁; here the only type of any
-- Kind(g) is Type itself
theorem one_type (β : Book) (hβ : Book.Closed β) (L : LHS) (sp : List Term) (q : Quant)
    (Γ : Ctx) (g T : Term) (π : Uses) (u : Term)
    (h : Check β (Pol.std β) L sp q Γ (.Typ g) T π u) :
    Le β (Ctx.δ Γ 0 type) (Ctx.δ Γ 0 T) := by
  obtain ⟨_, _, hc, _, _⟩ := Check.typ_inv (Pol.std_pre hβ) h
  exact hc

-- ----------------------------------------------------------------------------
-- (2) the identity at its own universe
-- ----------------------------------------------------------------------------

-- Empty: a family of kind Type with no constructor
def emptyD : AdtD := ⟨0, type, []⟩

-- id : (-X: Type) -> X -> X, filled by X => x => x. The type parameter is
-- erased; the value is Lone
def idTy : Term := .All .None type (.All .Lone (.Var 0) (.Var 1))
def idD : DefD := ⟨2, [.None, .Lone], idTy, .Lam (.Lam (.Var 0))⟩

-- Empty at 0, id at 1
def book : Book := [.adt emptyD, .defn idD]

-- Type : Kind(&0): an erased binder may range over Type (compare LE at
-- Typ: KLe's lone case, &0 being literal and not &2)
theorem type_in_kind_none (β : Book) (L : LHS) (Γ : Ctx) :
    Check β (Pol.std β) L [] .None Γ type (.Typ (.Qua .None)) Uses.zero .Qnt :=
  Check.cnv (Check.typ Check.qua) (by
    show Le β (Ctx.δ Γ 0 type) (Ctx.δ Γ 0 (.Typ (.Qua .None)))
    rw [Ctx.δ_closed _ _ type (by simp [type, Term.Closed]),
      Ctx.δ_closed _ _ (.Typ (.Qua .None)) (by simp [Term.Closed])]
    exact Le.typ (KLe.lone Red.refl (by decide)))

-- idTy : Type, checked dead: infer-all twice, the domains Type and X
theorem idTy_ok (β : Book) (L : LHS) (Γ : Ctx) :
    Check β (Pol.std β) L [] .None Γ idTy type Uses.zero .Qnt :=
  Check.all (type_in_kind_none β L Γ)
    (Check.all (Check.var (b := ⟨.None, type, none⟩) rfl)
      (Check.var (b := ⟨.None, type, none⟩) rfl))

-- the body X => x => x checks live at idTy under the def's own equation:
-- x is used once, X not at all
theorem id_body_ok (β : Book) (L : LHS) :
    Check β (Pol.std β) L [] .Lone [] (.Lam (.Lam (.Var 0))) idTy
      (Uses.tail (Uses.tail (Uses.one 0 .Lone))) (.Lam (.Lam (.Var 0))) :=
  Check.lam (type_in_kind_none β L [])
    (Check.lam (Check.var (b := ⟨.None, type, none⟩) rfl)
      (Check.var (b := ⟨.Lone, .Var 1, none⟩) rfl) (by simp [Uses.one, Quant.le]))
    (by simp [Uses.one, Uses.tail, Quant.le])

theorem id_ok : Book.Ok book := by
  intro k t hk
  match k, hk with
  | 0, hk =>
    cases hk
    refine ⟨⟨Uses.zero, Check.typ Check.qua⟩, .Qua .Lone, Red.refl, ?_⟩
    intro c C hc
    cases c <;> simp [emptyD, AdtD.ctr, AdtD.ctr.go] at hc
  | 1, hk =>
    cases hk
    refine ⟨⟨Uses.zero, idTy_ok _ _ _⟩, ?_, ?_, ?_, ⟨_, _, id_body_ok _ _⟩⟩
    · exact .cons Red.refl (.cons Red.refl .nil)
    · exact .lam (.lam .leaf)
    · trivial
  | k + 2, hk => cases k <;> simp [book, Book.tld] at hk

-- id(Type, Type) : Type, live and closed: the identity instantiated at the
-- universe it ranges over, then applied to that universe. The elaboration
-- erases the type argument and keeps the value, Type itself
theorem id_at_type :
    Check book (Pol.std book) (LHS.void book) [] .Lone [] (.App (.App (.Ref 1) type) type) type
      Uses.zero (.App (.App (.Ref 1) .Qnt) (.Typ .Qnt)) :=
  Check.app (B := type)
    (Check.app (q' := .None) (B := .All .Lone (.Var 0) (.Var 1))
      (Check.ref (d := idD) rfl (fun _ => by simp [LHS.void, book]) (fun _ h => by simp [LHS.void, book] at h))
      (Check.typ Check.qua))
    (Check.typ Check.qua)

-- ----------------------------------------------------------------------------
-- (3) Hurkens' universe is a Type
-- ----------------------------------------------------------------------------

-- P(X) = X -> Type, the powerset; the codomain is closed, so X is read at
-- the depth of the domain
def pow (X : Term) : Term := .All .Lone X type

-- U = (-X: Type) -> (P(P(X)) -> X) -> P(P(X)), Hurkens' universe: under X
-- the first arrow's domain sees X as 0 and its codomain as 1
def hurkensU : Term :=
  .All .None type (.All .Lone (.All .Lone (pow (pow (.Var 0))) (.Var 1)) (pow (pow (.Var 1))))

-- X : Type in the context that binds it at i
theorem var_type (β : Book) (L : LHS) (Γ : Ctx) (i : Nat) (b : Bind)
    (hb : Ctx.get Γ i = some b) (hT : b.T = type) :
    Check β (Pol.std β) L [] .None Γ (.Var i) type (Uses.one i .None) .Qnt :=
  hT ▸ Check.var hb

-- P(X) : Type whenever X : Type
theorem pow_ok (β : Book) (L : LHS) (Γ : Ctx) (X : Term) (π : Uses)
    (hX : Check β (Pol.std β) L [] .None Γ X type π .Qnt) :
    Check β (Pol.std β) L [] .None Γ (pow X) type Uses.zero .Qnt :=
  Check.all hX (Check.typ Check.qua)

theorem hurkensU_ok (β : Book) (L : LHS) (Γ : Ctx) :
    Check β (Pol.std β) L [] .None Γ hurkensU type Uses.zero .Qnt :=
  Check.all (type_in_kind_none β L Γ)
    (Check.all
      (Check.all
        (pow_ok _ _ _ _ _ (pow_ok _ _ _ _ _ (var_type _ _ _ 0 ⟨.None, type, none⟩ rfl rfl)))
        (var_type _ _ _ 1 ⟨.None, type, none⟩ rfl rfl))
      (pow_ok _ _ _ _ _ (pow_ok _ _ _ _ _ (var_type _ _ _ 1 ⟨.None, type, none⟩ rfl rfl))))

-- and so it is a Type in the book, dead or live (a type is dead code, but
-- the universe rule does not care)
theorem hurkensU_type (L : LHS) (sp : List Term) (Γ : Ctx) :
    ∃ π u, Check book (Pol.std book) L sp .Lone Γ hurkensU type π u :=
  ⟨_, _, Check.all (type_in_kind_none book L Γ) (Check.all
      (Check.all
        (pow_ok _ _ _ _ _ (pow_ok _ _ _ _ _ (var_type _ _ _ 0 ⟨.None, type, none⟩ rfl rfl)))
        (var_type _ _ _ 1 ⟨.None, type, none⟩ rfl rfl))
      (pow_ok _ _ _ _ _ (pow_ok _ _ _ _ _ (var_type _ _ _ 1 ⟨.None, type, none⟩ rfl rfl))))⟩

-- ----------------------------------------------------------------------------
-- (4) the paradox's conclusion has no proof
-- ----------------------------------------------------------------------------

-- False, impredicatively: (-X: Type) -> X, a Type by the same rule
def false : Term := .All .None type (.Var 0)

theorem false_ok (β : Book) (L : LHS) (Γ : Ctx) :
    Check β (Pol.std β) L [] .None Γ false type Uses.zero .Qnt :=
  Check.all (type_in_kind_none β L Γ) (var_type _ _ _ 0 ⟨.None, type, none⟩ rfl rfl)

-- Empty is empty
theorem empty_empty : Book.empty book 0 [] :=
  ⟨emptyD, rfl, fun c hc => absurd hc (by simp [emptyD])⟩

-- a closed live proof of False would be, applied to Empty, a closed live
-- term of Empty, which consistency_holds refutes. The application is a
-- live infer-app with a dead type argument
theorem no_proof_of_false (t : Term) (π : Uses) (u : Term) :
    ¬ Check book (Pol.std book) (LHS.void book) [] .Lone [] t false π u := by
  intro h
  have h' : Check book (Pol.std book) (LHS.void book) [] .Lone [] (.App t (.Adt 0 []))
      (Term.subst 0 (.Adt 0 []) (.Var 0)) (Uses.add π Uses.zero)
      (.App u (Term.era .None (.Adt 0 []))) :=
    Check.app (q' := .None) (Check.sp h [.Adt 0 []]) (Check.adt (A := emptyD) rfl)
  exact consistency_holds book 0 [] [] _ _ _ id_ok empty_empty h'

end Universe
end BendCore

#print axioms BendCore.Universe.type_in_type
#print axioms BendCore.Universe.one_type
#print axioms BendCore.Universe.id_ok
#print axioms BendCore.Universe.id_at_type
#print axioms BendCore.Universe.hurkensU_ok
#print axioms BendCore.Universe.no_proof_of_false
