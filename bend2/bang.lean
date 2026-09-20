-- ============================================================================
-- BANG — the exponential ! in bend-core: the judgment with a ! binder, and
-- what holds of it
-- ============================================================================
--
-- bend.ts's ! (its THEORY note) is a fourth binder quantity next to -, plain
-- and +: a ! binder is reusable at any kind, and its argument pays, being
-- closed (no live use) or a ! variable passed on; so its value is a recipe,
-- a closed term the callee may run any number of times, as it may call a
-- def. ! marks a def's parameter (a law's clause) or a let, never a type:
-- no field, no datatype parameter, no @!x:A -> B, so a def with a !
-- parameter is called, never held, and no datatype carries a recipe.
--
-- bend.lean carries Bang in Quant but inert: no base rule binds a ! (le _
-- Bang is False, so a lam or let closes a ! binder only unused), no literal
-- spells it (Check.qua), and a ! field asks Data of its domain (Quant.data),
-- so the five claims hold of the base judgment unchanged. This file states
-- the judgment WITH the ! rules, CheckB, mirroring bend.ts rule for rule:
--
--   lam, let   a ! binder asks Type of its domain (Quant.kind) and accepts
--              any measure (Quant.leB)
--   app, let   an argument to a ! binder, in a live region, is Promoted:
--              its measure is all None (term_promote's loop), or it is a
--              variable bound !
--   all        no ! binder in a type (infer-all's refusal)
--   mat, efq   no ! scrutinee (check-mat's refusal)
--   BookB.Ok   a def's type is a telescope whose leading binders may be !
--              (def_type_check); a constructor's binders are never !
--              (parse_tele's refusal)
--
-- and proves what the design was argued from:
--
--   recipe_captureless   a promoted argument's certified term mentions no
--                        variable: the closure the compiler builds captures
--                        nothing, which is why the runtime shares it for
--                        free
--   all_no_bang          no checked type has a ! binder at its head
--   never_held           a def whose type starts with a ! binder converts
--                        to no plain function type: it is called, never
--                        passed
--   bang_arg             an argument handed to a ! def is Promoted
--   base_fragment        a CheckB derivation that never meets a ! binder is
--                        a Check derivation: the extension is conservative
--                        on the base fragment
--
-- The claims of bend.lean §11 for CheckB (in particular consistency: no
-- closed live term of an emptied family in a BookB.Ok book) are STATED here
-- and not proved: the pricing argument of §N reads a copied value as Data,
-- and a recipe is a closed function instead. The argument for it is the
-- one bend.ts's note gives, closed terms name earlier defs, so the book's
-- recursion stays the descent's; mechanizing it is future work.
--
-- To check:  lean -o bend.olean bend.lean; LEAN_PATH=. lean bang.lean

import bend

namespace BendCore
namespace Bang

-- ----------------------------------------------------------------------------
-- The ! quantity's algebra
-- ----------------------------------------------------------------------------

-- the kind a binder asks of its domain: a ! binder is reusable at any kind,
-- so it asks Type as a plain binder does (bend.ts quant_kind)
def Quant.kind : Quant → Quant
  | .Bang => .Lone
  | q     => q

-- a measure fits a ! binder whatever it is; else as the base
def Quant.leB (x q : Quant) : Prop := q = .Bang ∨ Quant.le x q

-- a ! argument (bend.ts term_promote): no live use, or a ! variable
def Promoted (Γ : Ctx) (x : Term) (π : Uses) : Prop :=
  (∀ i, π i = .None) ∨ ∃ i b, x = .Var i ∧ Ctx.get Γ i = some b ∧ b.q = .Bang

-- ----------------------------------------------------------------------------
-- The judgment (bend.lean §9 with the ! rules)
-- ----------------------------------------------------------------------------

inductive CheckB (β : Book) (Φ : Pol) :
    LHS → List Term → Quant → Ctx → Term → Term → Uses → Term → Prop
  | var : Ctx.get Γ i = some b →
          CheckB β Φ L sp q Γ (.Var i) b.T (Uses.one i q) (Term.era q (.Var i))
  | ref : Book.defn β j = some d →
          (q ≠ .None → j ≤ L.k) →
          (q ≠ .None → j = L.k →
            SpineLt β L.qs 0 (L.cols.map (Ctx.δ Γ 0)) (sp.map (Ctx.δ Γ 0))) →
          CheckB β Φ L sp q Γ (.Ref j) d.ty Uses.zero (Term.era q (.Ref j))
  | refA : Book.adt β k = some A → A.pn = 0 →
           CheckB β Φ L sp q Γ (.Ref k) A.sig Uses.zero (Term.era q (.Ref k))
  | adt : Book.adt β a = some A →
          CheckB β Φ L sp q Γ (.Adt a r) A.sig Uses.zero (Term.era q (.Adt a r))
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C → c ∉ r →
          CheckB β Φ L sp q Γ (.Ctr a c) (Term.retip r A.pn (A.pn + C.fn) C.ty) Uses.zero
            (Term.era q (.Ctr a c))
  | typ : CheckB β Φ L [] .None Γ g .Qnt πg .Qnt →
          CheckB β Φ L sp q Γ (.Typ g) (.Typ (.Qua .Lone)) Uses.zero
            (Term.era q (.Typ .Qnt))
  | qnt : CheckB β Φ L sp q Γ .Qnt (.Typ (.Qua .Lone)) Uses.zero .Qnt
  | qua : q' ≠ .Bang → CheckB β Φ L sp q Γ (.Qua q') .Qnt Uses.zero (Term.era q (.Qua q'))
  | min : CheckB β Φ L [] q Γ a .Qnt πa ua →
          CheckB β Φ L [] q Γ b .Qnt πb ub →
          CheckB β Φ L sp q Γ (.Min a b) .Qnt (Uses.add πa πb) (Term.era q (.Min ua ub))
  -- no ! binder in a type (infer-all)
  | all : q' ≠ .Bang →
          CheckB β Φ L [] .None Γ A (.Typ (.Qua q')) πA .Qnt →
          CheckB β Φ L.shift [] .None (⟨q', A, none⟩ :: Γ) B (.Typ (.Qua .Lone)) πB .Qnt →
          CheckB β Φ L sp q Γ (.All q' A B) (.Typ (.Qua .Lone)) Uses.zero
            (Term.era q (.All q' .Qnt .Qnt))
  -- a ! binder asks Type of its domain and accepts any measure (check-lam)
  | lam : CheckB β Φ L [] .None Γ A (.Typ (.Qua (Quant.kind q'))) πA .Qnt →
          CheckB β Φ L.lam [] q (⟨q', A, none⟩ :: Γ) f B π uf →
          Quant.leB (π 0) q' →
          CheckB β Φ L sp q Γ (.Lam f) (.All q' A B) (Uses.tail π) (Term.era q (.Lam uf))
  -- an argument to a ! binder is Promoted in a live region (infer-app)
  | app : CheckB β Φ L (x :: sp) q Γ f (.All q' A B) πf uf →
          CheckB β Φ L [] (Quant.dem q' q) Γ x A πx ux →
          (q' = .Bang → q ≠ .None → Promoted Γ x πx) →
          CheckB β Φ L sp q Γ (.App f x) (Term.subst 0 x B) (Uses.add πf πx)
            (Term.era q (.App uf ux))
  | appLam : Term.Closed Γ.length a →
             CheckB β Φ L sp q Γ (Term.subst 0 a f) T π u →
             CheckB β Φ L sp q Γ (.App (.Lam f) a) T π u
  -- a ! let: its value Promoted, its binder as check-lam's (check-let)
  | let_ : CheckB β Φ L [] (Quant.dem qb q) Γ v A πv uv →
           CheckB β Φ L [] .None Γ A (.Typ (.Qua (Quant.kind qb))) πA .Qnt →
           CheckB β Φ L.shift [] q (⟨qb, A, some v⟩ :: Γ) b (Term.shift 0 T) π ub →
           Quant.leB (π 0) qb →
           (qb = .Bang → q ≠ .None → Promoted Γ v πv) →
           CheckB β Φ L sp q Γ (.Let qb v b) T (Uses.add πv (Uses.tail π))
             (Term.era q (.Let qb uv ub))
  | eql : CheckB β Φ L [] .None Γ T (.Typ (.Qua .Lone)) πT .Qnt →
          CheckB β Φ L [] .None Γ a T πa .Qnt →
          CheckB β Φ L [] .None Γ b T πb .Qnt →
          CheckB β Φ L sp q Γ (.Eql a b T) (.Typ (.Qua .Many)) Uses.zero
            (Term.era q (.Eql .Qnt .Qnt .Qnt))
  | rfl : Conv β (Ctx.δ Γ 0 a) (Ctx.δ Γ 0 b) →
          CheckB β Φ L sp q Γ .Rfl (.Eql a b T) Uses.zero (Term.era q .Rfl)
  | rwt : CheckB β Φ L [] q Γ e (.Eql a b T) πe ue →
          CheckB β Φ L [] .None Γ P (Term.jmotive a T) πP .Qnt →
          CheckB β Φ L [] q Γ f (.App (.App P a) .Rfl) πf uf →
          CheckB β Φ L sp q Γ (.Rwt e P f) (.App (.App P b) e) (Uses.add πe πf)
            (Term.era q (.Rwt ue .Qnt uf))
  -- no ! scrutinee (check-mat, check-efq)
  | mat : Book.adt β a = some A → AdtD.ctr A c = some C →
          c ∉ r → ps.length = A.pn →
          (q ≠ .None → q' ≠ .None) → q' ≠ .Bang →
          Insts C.ty ps telF →
          MatGoal q' C.fn B (Term.apps (.Ctr a c) ps) telF G →
          CheckB β Φ (L.mat a c C.fn) [] q Γ h G πh uh →
          CheckB β Φ L [] q Γ m (.All q' (Term.apps (.Adt a (c :: r)) ps) B) πm um →
          CheckB β Φ L sp q Γ (.Mat a c h m) (.All q' (Term.apps (.Adt a r) ps) B)
            (Uses.join πh πm) (Term.era q (.Mat a c uh um))
  | efq : Book.adt β a = some A →
          (q ≠ .None → q' ≠ .None) → q' ≠ .Bang →
          (Book.empty β a r ∨ Φ.efq Γ) →
          CheckB β Φ L sp q Γ .Efq (.All q' (Term.apps (.Adt a r) ps) B) Uses.zero
            (Term.era q .Efq)
  | cnv : CheckB β Φ L sp q Γ t A π u → Φ.conv (Ctx.δ Γ 0 A) (Ctx.δ Γ 0 B) →
          CheckB β Φ L sp q Γ t B π u

-- ----------------------------------------------------------------------------
-- The book (bend.lean §10 with the ! rules)
-- ----------------------------------------------------------------------------

-- adt_valid's constructor walk: no binder is ! (parse_tele refuses a !
-- field or datatype parameter), else as CtrOk
def CtrOkB (β : Book) (k pn : Nat) (G : Term) : Ctx → Nat → Term → Prop
  | Γ, i, .All q A B =>
      q ≠ .Bang ∧
      (∃ π, CheckB β (Pol.std β) ⟨k, .Ref k, 0, []⟩ [] .None Γ A
        (.Typ (if pn ≤ i ∧ q = .Lone then Term.shiftN (i - pn) G else .Qua q)) π .Qnt) ∧
      CtrOkB β k pn G (⟨q, A, none⟩ :: Γ) (i + 1) B
  | _, _, _ => True

-- a def's type (def_type_check): its n leading binders one by one, a !
-- one asking Type of its domain, then the rest as a type; so a ! binder
-- lives in a def's telescope alone
def DefTy (β : Book) : LHS → Ctx → Nat → Term → Prop
  | L, Γ, 0, T =>
      ∃ π, CheckB β (Pol.std β) L [] .None Γ T (.Typ (.Qua .Lone)) π .Qnt
  | L, Γ, n + 1, .All q A B =>
      (∃ π, CheckB β (Pol.std β) L [] .None Γ A (.Typ (.Qua (Quant.kind q))) π .Qnt) ∧
      DefTy β L.shift (⟨q, A, none⟩ :: Γ) n B
  | _, _, _ + 1, _ => False

def BookB.Ok (β : Book) : Prop :=
  ∀ k t, Book.tld β k = some t →
    match t with
    | .adt A =>
        (∃ π, CheckB β (Pol.std β) ⟨k, .Ref k, 0, []⟩ [] .None [] A.sig
          (.Typ (.Qua .Lone)) π .Qnt) ∧
        ∃ G, STele β A.pn A.sig G ∧
        ∀ c C, AdtD.ctr A c = some C →
          CtrD.Shape k A.pn C ∧ CtrOkB β k A.pn G [] 0 C.ty
    | .defn d =>
        DefTy β ⟨k, .Ref k, 0, []⟩ [] d.n d.ty ∧
        TeleQs β d.ty d.n d.qs ∧
        Tree β d.n d.body ∧ Term.CtrsFull β 0 d.body ∧
        ∃ π u, CheckB β (Pol.std β) ⟨k, .Ref k, d.n, d.qs⟩ [] .Lone [] d.body d.ty π u

-- the claim, stated (bend.lean §11's consistency, for CheckB): not proved
-- here, see the header
def bang_consistency : Prop :=
  ∀ (β : Book) (a : Nat) (r : List Nat) (ps : List Term)
    (t : Term) (π : Uses) (u : Term),
    BookB.Ok β → Book.empty β a r →
    ¬ CheckB β (Pol.std β) (LHS.void β) [] .Lone [] t (Term.apps (.Adt a r) ps) π u

-- ----------------------------------------------------------------------------
-- The measure: as bend.lean §D1/§N3, rule for rule
-- ----------------------------------------------------------------------------

theorem CheckB.uses_ge {sp : List Term} (h : CheckB β Φ L sp q Γ t T π u) :
    ∀ i, Γ.length ≤ i → π i = .None := by
  induction h with
  | var hg =>
    intro i hi
    have := Ctx.get_lt hg
    simp only [Uses.one]; rw [if_neg (by omega)]
  | min _ _ iha ihb => intro i hi; simp only [Uses.add, iha i hi, ihb i hi]; rfl
  | lam _ _ _ _ ihf => intro i hi; exact ihf (i + 1) (by simp only [List.length_cons]; omega)
  | app _ _ _ ihf ihx => intro i hi; simp only [Uses.add, ihf i hi, ihx i hi]; rfl
  | appLam _ _ ih => exact ih
  | let_ _ _ _ _ _ ihv _ ihb =>
    intro i hi
    simp only [Uses.add, Uses.tail, ihv i hi, ihb (i + 1) (by simp only [List.length_cons]; omega)]
    rfl
  | rwt _ _ _ ihe _ ihf => intro i hi; simp only [Uses.add, ihe i hi, ihf i hi]; rfl
  | mat _ _ _ _ _ _ _ _ _ _ ihh ihm => intro i hi; simp only [Uses.join, ihh i hi, ihm i hi]; rfl
  | cnv _ _ ih => exact ih
  | _ => intro _ _; rfl

theorem CheckB.occ {sp : List Term} (h : CheckB β Φ L sp q Γ t T π u) (i : Nat) :
    (π i = .None → Term.occ i u = 0) ∧ (π i = .Lone → Term.occ i u ≤ 1) := by
  induction h generalizing i with
  | var _ =>
    refine ⟨fun hh => ?_, fun hh => ?_⟩ <;> simp only [Uses.one] at hh <;> split at hh
    · subst hh; simp [Term.era, Term.occ]
    · exact Nat.le_zero.mp (Nat.le_trans (Term.occ_era_le _ _ _)
        (by simp only [Term.occ]; split <;> omega))
    · subst hh
      exact Nat.le_trans (Term.occ_era_le _ _ _) (by simp only [Term.occ]; split <;> omega)
    · exact absurd hh (by simp)
  | min _ _ iha ihb => exact Quant.occ_mono (Quant.occ_add (iha i) (ihb i)) (Term.occ_era_le _ _ _)
  | lam _ _ _ _ ihf => exact Quant.occ_mono (ihf (i + 1)) (Term.occ_era_le _ _ _)
  | app _ _ _ ihf ihx => exact Quant.occ_mono (Quant.occ_add (ihf i) (ihx i)) (Term.occ_era_le _ _ _)
  | appLam _ _ ih => exact ih i
  | let_ _ _ _ _ _ ihv _ ihb =>
    exact Quant.occ_mono (Quant.occ_add (ihv i) (ihb (i + 1))) (Term.occ_era_le _ _ _)
  | rwt _ _ _ ihe _ ihf =>
    exact Quant.occ_mono (Quant.occ_add (ihe i) (ihf i)) (Term.occ_era_le _ _ _)
  | mat _ _ _ _ _ _ _ _ _ _ ihh ihm =>
    exact Quant.occ_mono (Quant.occ_join (ihh i) (ihm i)) (Term.occ_era_le _ _ _)
  | cnv _ _ ih => exact ih i
  | qnt => exact ⟨fun _ => _root_.rfl, fun h => by simp [Uses.zero] at h⟩
  | _ =>
    exact ⟨fun _ => Nat.le_zero.mp (Nat.le_trans (Term.occ_era_le _ _ _) (by simp [Term.occ])),
      fun h => by simp [Uses.zero] at h⟩

-- a promoted argument's certified term mentions no variable: the closure
-- the compiler builds of it (_ => a) captures nothing
theorem CheckB.recipe_captureless {sp : List Term} (h : CheckB β Φ L sp q Γ x A π u)
    (hp : ∀ i, π i = .None) : ∀ i, Term.occ i u = 0 :=
  fun i => (h.occ i).1 (hp i)

-- ----------------------------------------------------------------------------
-- Generation (bend.lean §E), for the rules the design rests on
-- ----------------------------------------------------------------------------

-- no checked type has a ! binder at its head
theorem CheckB.all_no_bang {sp : List Term}
    (h : CheckB β Φ L sp q Γ (.All q' A B) T π u) : q' ≠ .Bang := by
  generalize he : Term.All q' A B = t0 at h
  induction h <;> try exact Term.noConfusion he
  case all hne _ _ _ _ => cases he; exact hne
  case cnv _ _ ih => exact ih he

theorem CheckB.ref_inv (hΦ : Pol.Pre Φ) {sp : List Term}
    (h : CheckB β Φ L sp q Γ (.Ref j) T π u) :
    (∃ d, Book.defn β j = some d ∧ Φ.conv (Ctx.δ Γ 0 d.ty) (Ctx.δ Γ 0 T)) ∨
    (∃ A, Book.adt β j = some A ∧ A.pn = 0 ∧ Φ.conv (Ctx.δ Γ 0 A.sig) (Ctx.δ Γ 0 T)) := by
  generalize he : Term.Ref j = t0 at h
  induction h <;> try exact Term.noConfusion he
  case ref hk _ _ => cases he; exact .inl ⟨_, hk, hΦ.refl _⟩
  case refA hk h0 => cases he; exact .inr ⟨_, hk, h0, hΦ.refl _⟩
  case cnv _ hc ih =>
    rcases ih he with ⟨d, hk, hcv⟩ | ⟨A, hk, h0, hcv⟩
    · exact .inl ⟨d, hk, hΦ.trans hcv hc⟩
    · exact .inr ⟨A, hk, h0, hΦ.trans hcv hc⟩

theorem CheckB.app_inv (hΦ : Pol.Pre Φ) {sp : List Term}
    (h : CheckB β Φ L sp q Γ (.App f x) T π u) :
    (∃ q' A B πf uf πx ux, CheckB β Φ L (x :: sp) q Γ f (.All q' A B) πf uf ∧
      CheckB β Φ L [] (Quant.dem q' q) Γ x A πx ux ∧
      (q' = .Bang → q ≠ .None → Promoted Γ x πx) ∧
      Φ.conv (Ctx.δ Γ 0 (Term.subst 0 x B)) (Ctx.δ Γ 0 T)) ∨
    (∃ g, f = .Lam g) := by
  generalize he : Term.App f x = t0 at h
  induction h <;> try exact Term.noConfusion he
  case app hf hx hp _ _ => cases he; exact .inl ⟨_, _, _, _, _, _, _, hf, hx, hp, hΦ.refl _⟩
  case appLam _ _ _ => cases he; exact .inr ⟨_, _root_.rfl⟩
  case cnv _ hc ih =>
    rcases ih he with ⟨q', A, B, πf, uf, πx, ux, hf, hx, hp, hcv⟩ | hl
    · exact .inl ⟨q', A, B, πf, uf, πx, ux, hf, hx, hp, hΦ.trans hcv hc⟩
    · exact .inr hl

-- a def whose type starts with a ! binder converts to no plain function
-- type: it is called, never passed to a plain binder
theorem CheckB.never_held (hβ : Book.Closed β) {sp : List Term}
    (h : CheckB β (Pol.std β) L sp q Γ (.Ref j) T π u)
    (hk : Book.defn β j = some d) (hd : d.ty = .All .Bang A B)
    (hT : Le β (Ctx.δ Γ 0 T) (.All q' A' B')) : q' = .Bang := by
  rcases CheckB.ref_inv (Pol.std_pre hβ) h with ⟨d', hk', hcv⟩ | ⟨A0, hk0, _, _⟩
  · rw [hk] at hk'; cases hk'
    rw [hd, Ctx.δ_all] at hcv
    have hle : Le β (.All .Bang (Ctx.δ Γ 0 A) (Ctx.δ Γ 1 B)) (.All q' A' B') :=
      Le.trans hβ hcv hT
    exact (Le.all_inv hβ hle Red.refl Red.refl).1.symm
  · exact absurd (Book.adt_tld hk0) (by rw [Book.defn_tld hk]; simp)

-- an argument handed to a ! def, in a live region, is Promoted: closed, or
-- a ! variable
theorem CheckB.bang_arg (hβ : Book.Closed β) {sp : List Term}
    (h : CheckB β (Pol.std β) L sp q Γ (.App (.Ref j) x) T π u)
    (hk : Book.defn β j = some d) (hd : d.ty = .All .Bang A B) (hq : q ≠ .None) :
    ∃ πx ux A', CheckB β (Pol.std β) L [] q Γ x A' πx ux ∧ Promoted Γ x πx := by
  rcases CheckB.app_inv (Pol.std_pre hβ) h with ⟨q', A', B', _, _, πx, ux, hf, hx, hp, _⟩ | ⟨_, hl⟩
  · have hq' : q' = .Bang :=
      CheckB.never_held hβ hf hk hd (by rw [Ctx.δ_all]; exact Le.refl _)
    subst hq'
    exact ⟨πx, ux, A', hx, hp _root_.rfl hq⟩
  · exact Term.noConfusion hl

-- a constructor binds no !: no datatype carries a recipe
theorem CtrOkB.no_bang (h : CtrOkB β k pn G Γ i (.All q A B)) : q ≠ .Bang := h.1

-- ----------------------------------------------------------------------------
-- The base fragment: a derivation that meets no ! binder is a Check
-- derivation, so the extension is conservative over the base judgment
-- ----------------------------------------------------------------------------

-- a derivation meets a ! binder at a lam, a let, or an app or mat whose
-- function type binds !; this says it never does
inductive NoBang (β : Book) (Φ : Pol) :
    ∀ {L sp q Γ t T π u}, CheckB β Φ L sp q Γ t T π u → Prop
  | var {Γ i b L sp q} (hg : Ctx.get Γ i = some b) : NoBang β Φ (.var (L := L) (sp := sp) (q := q) hg)
  | ref {j d L sp q Γ} (hk) (h1) (h2) : NoBang β Φ (.ref (j := j) (d := d) (L := L) (sp := sp) (q := q) (Γ := Γ) hk h1 h2)
  | refA {k A L sp q Γ} (hk) (h0) : NoBang β Φ (.refA (k := k) (A := A) (L := L) (sp := sp) (q := q) (Γ := Γ) hk h0)
  | adt {a A r L sp q Γ} (hk) : NoBang β Φ (.adt (a := a) (A := A) (r := r) (L := L) (sp := sp) (q := q) (Γ := Γ) hk)
  | ctr {a A c C r L sp q Γ} (hk) (hc) (hr) : NoBang β Φ (.ctr (a := a) (A := A) (c := c) (C := C) (r := r) (L := L) (sp := sp) (q := q) (Γ := Γ) hk hc hr)
  | typ {L Γ g πg sp q} {hg : CheckB β Φ L [] .None Γ g .Qnt πg .Qnt} :
      NoBang β Φ hg → NoBang β Φ (.typ (sp := sp) (q := q) hg)
  | qnt {L sp q Γ} : NoBang β Φ (.qnt (L := L) (sp := sp) (q := q) (Γ := Γ))
  | qua {L sp q Γ q'} (hq : q' ≠ Quant.Bang) : NoBang β Φ (.qua (L := L) (sp := sp) (q := q) (Γ := Γ) hq)
  | min {L q Γ a πa ua b πb ub sp} {ha : CheckB β Φ L [] q Γ a .Qnt πa ua}
      {hb : CheckB β Φ L [] q Γ b .Qnt πb ub} :
      NoBang β Φ ha → NoBang β Φ hb → NoBang β Φ (.min (sp := sp) ha hb)
  | all {L Γ q' A πA B πB sp q} (hne : q' ≠ Quant.Bang)
      {hA : CheckB β Φ L [] .None Γ A (.Typ (.Qua q')) πA .Qnt}
      {hB : CheckB β Φ L.shift [] .None (⟨q', A, none⟩ :: Γ) B (.Typ (.Qua .Lone)) πB .Qnt} :
      NoBang β Φ hA → NoBang β Φ hB → NoBang β Φ (.all (sp := sp) (q := q) hne hA hB)
  | lam {L Γ q' A πA q f B π uf sp} (hne : q' ≠ Quant.Bang)
      {hA : CheckB β Φ L [] .None Γ A (.Typ (.Qua (Quant.kind q'))) πA .Qnt}
      {hf : CheckB β Φ L.lam [] q (⟨q', A, none⟩ :: Γ) f B π uf} (hle : Quant.leB (π 0) q') :
      NoBang β Φ hA → NoBang β Φ hf → NoBang β Φ (.lam (sp := sp) hA hf hle)
  | app {L x sp q Γ f q' A B πf uf πx ux} (hne : q' ≠ Quant.Bang)
      {hf : CheckB β Φ L (x :: sp) q Γ f (.All q' A B) πf uf}
      {hx : CheckB β Φ L [] (Quant.dem q' q) Γ x A πx ux} (hp) :
      NoBang β Φ hf → NoBang β Φ hx → NoBang β Φ (.app hf hx hp)
  | appLam {Γ a L sp q f T π u} (ha : Term.Closed Γ.length a)
      {hb : CheckB β Φ L sp q Γ (Term.subst 0 a f) T π u} :
      NoBang β Φ hb → NoBang β Φ (.appLam ha hb)
  | let_ {L qb q Γ v A πv uv πA b T π ub sp} (hne : qb ≠ Quant.Bang)
      {hv : CheckB β Φ L [] (Quant.dem qb q) Γ v A πv uv}
      {hA : CheckB β Φ L [] .None Γ A (.Typ (.Qua (Quant.kind qb))) πA .Qnt}
      {hb : CheckB β Φ L.shift [] q (⟨qb, A, some v⟩ :: Γ) b (Term.shift 0 T) π ub}
      (hle : Quant.leB (π 0) qb) (hp) :
      NoBang β Φ hv → NoBang β Φ hA → NoBang β Φ hb → NoBang β Φ (.let_ (sp := sp) hv hA hb hle hp)
  | eql {L Γ T πT a πa b πb sp q}
      {hT : CheckB β Φ L [] .None Γ T (.Typ (.Qua .Lone)) πT .Qnt}
      {ha : CheckB β Φ L [] .None Γ a T πa .Qnt} {hb : CheckB β Φ L [] .None Γ b T πb .Qnt} :
      NoBang β Φ hT → NoBang β Φ ha → NoBang β Φ hb → NoBang β Φ (.eql (sp := sp) (q := q) hT ha hb)
  | rfl {Γ a b L sp q T} (hc : Conv β (Ctx.δ Γ 0 a) (Ctx.δ Γ 0 b)) :
      NoBang β Φ (.rfl (L := L) (sp := sp) (q := q) (T := T) hc)
  | rwt {L q Γ e a b T πe ue P πP f πf uf sp}
      {he : CheckB β Φ L [] q Γ e (.Eql a b T) πe ue}
      {hP : CheckB β Φ L [] .None Γ P (Term.jmotive a T) πP .Qnt}
      {hf : CheckB β Φ L [] q Γ f (.App (.App P a) .Rfl) πf uf} :
      NoBang β Φ he → NoBang β Φ hP → NoBang β Φ hf → NoBang β Φ (.rwt (sp := sp) he hP hf)
  | mat {a A c C r ps q q' telF B G L Γ h πh uh m πm um sp}
      (hk : Book.adt β a = some A) (hc : AdtD.ctr A c = some C) (hr : c ∉ r) (hps : ps.length = A.pn)
      (hlive : q ≠ Quant.None → q' ≠ Quant.None) (hnb : q' ≠ Quant.Bang) (hins : Insts C.ty ps telF)
      (hgoal : MatGoal q' C.fn B (Term.apps (.Ctr a c) ps) telF G)
      {hh : CheckB β Φ (L.mat a c C.fn) [] q Γ h G πh uh}
      {hm : CheckB β Φ L [] q Γ m (.All q' (Term.apps (.Adt a (c :: r)) ps) B) πm um} :
      NoBang β Φ hh → NoBang β Φ hm →
      NoBang β Φ (.mat (sp := sp) hk hc hr hps hlive hnb hins hgoal hh hm)
  | efq {a A q q' r Γ L sp ps B} (hk : Book.adt β a = some A) (hlive : q ≠ Quant.None → q' ≠ Quant.None)
      (hnb : q' ≠ Quant.Bang) (he : Book.empty β a r ∨ Φ.efq Γ) :
      NoBang β Φ (.efq (L := L) (sp := sp) (ps := ps) (B := B) hk hlive hnb he)
  | cnv {L sp q Γ t A π u B} {h : CheckB β Φ L sp q Γ t A π u}
      (hc : Φ.conv (Ctx.δ Γ 0 A) (Ctx.δ Γ 0 B)) : NoBang β Φ h → NoBang β Φ (.cnv h hc)

theorem Quant.kind_of_ne (h : q ≠ .Bang) : Quant.kind q = q := by
  cases q <;> simp_all [Quant.kind]

theorem Quant.leB_of_ne (h : q ≠ .Bang) (hle : Quant.leB x q) : Quant.le x q := by
  rcases hle with h' | h'
  · exact absurd h' h
  · exact h'

theorem NoBang.base {sp : List Term} {h : CheckB β Φ L sp q Γ t T π u} (hn : NoBang β Φ h) :
    Check β Φ L sp q Γ t T π u := by
  induction hn with
  | var hg => exact .var hg
  | ref hk h1 h2 => exact .ref hk h1 h2
  | refA hk h0 => exact .refA hk h0
  | adt hk => exact .adt hk
  | ctr hk hc hr => exact .ctr hk hc hr
  | typ _ ih => exact .typ ih
  | qnt => exact .qnt
  | qua hq => exact .qua hq
  | min _ _ iha ihb => exact .min iha ihb
  | all _ _ _ ihA ihB => exact .all ihA ihB
  | lam hne hle _ _ ihA ihf =>
    rw [Quant.kind_of_ne hne] at ihA
    exact .lam ihA ihf (Quant.leB_of_ne hne hle)
  | app _ _ _ _ ihf ihx => exact .app ihf ihx
  | appLam ha _ ih => exact .appLam ha ih
  | let_ hne hle _ _ _ _ ihv ihA ihb =>
    rw [Quant.kind_of_ne hne] at ihA
    exact .let_ ihv ihA ihb (Quant.leB_of_ne hne hle)
  | eql _ _ _ ihT iha ihb => exact .eql ihT iha ihb
  | rfl hc => exact .rfl hc
  | rwt _ _ _ ihe ihP ihf => exact .rwt ihe ihP ihf
  | mat hk hc hr hps hlive _ hins hgoal _ _ ihh ihm => exact .mat hk hc hr hps hlive hins hgoal ihh ihm
  | efq hk hlive _ he => exact .efq hk hlive he
  | cnv hc _ ih => exact .cnv ih hc

end Bang
end BendCore

#print axioms BendCore.Bang.CheckB.recipe_captureless
#print axioms BendCore.Bang.CheckB.all_no_bang
#print axioms BendCore.Bang.CheckB.never_held
#print axioms BendCore.Bang.CheckB.bang_arg
#print axioms BendCore.Bang.NoBang.base
