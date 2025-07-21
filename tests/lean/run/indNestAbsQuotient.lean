opaque T : (α : Type u) → [BEq α] → Type u

/--
warning: declaration uses 'sorry'
---
error: (kernel) application type mismatch
  @T Expr' sorry
argument has type
  _nested.BEq_1
but function has type
  [BEq Expr'] → Type
-/
#guard_msgs in
inductive Expr' where
  | leaf : Expr'
  | app : Expr' → @T Expr' sorry → Expr'

inductive T.Raw (α : Type u) : Type u where
  | mk : α → T.Raw α → T.Raw α -- pseudo-implementation, representative for any kernel-friendly type
deriving BEq

-- Abstract interface needed for the construction below

variable {α} {β}
variable [BEq α] [BEq β]

axiom T.WF : T.Raw α → Prop
axiom T.abs : (x : T.Raw α) → T.WF x → T α
axiom T.repr : T α → T.Raw α
axiom T.wf : (t : T α) → T.WF t.repr
axiom T.abs_repr {x : T α} : T.abs (T.repr x) (T.wf x) = x
axiom T.repr_abs {x : T.Raw α} {h : T.WF x} : T.repr (T.abs x h) = x
axiom T.Raw.map : (f : α → β) → T.Raw α → T.Raw β

-- Cannot be abstract, since we need to define a nested inductive predicate
inductive T.Raw.Forall (p : α → Prop) : T.Raw α → Prop
  | mk x xs : p x → xs.Forall p → T.Raw.Forall p (T.Raw.mk x xs)


axiom T.Raw.wf_map (f : α → β) (x : T.Raw α) (h : T.WF x) : T.WF (T.Raw.map f x)
axiom T.Raw.Forall_map {α : Type u} {β : Type v} (f : α → β) (p : β → Prop)
  (m : T.Raw α) (h : ∀ x, p (f x)) :
  T.Raw.Forall p (m.map f)
axiom T.Raw.attach {p : α → Prop} (m : T.Raw α) : T.Raw.Forall p m → T.Raw (Subtype p)
axiom T.Raw.wf_attach (x : T.Raw α) (h1 : T.WF x) {h2 : x.Forall p} : T.WF (x.attach h2)
axiom T.Raw.map_val_attach (x : T.Raw α) (h : T.Raw.Forall p x) :
  T.Raw.map Subtype.val (x.attach h) = x
axiom T.Raw.attach_map_val (x : T.Raw (Subtype p)) (h : T.Raw.Forall p (x.map Subtype.val)) :
  (T.Raw.map Subtype.val x).attach h = x


inductive Expr.Raw where
  | leaf : Expr.Raw
  | app : Expr.Raw → T.Raw Expr.Raw → Expr.Raw
deriving BEq

attribute [pp_nodot] Expr.Raw.app

-- inductive or def?

/- inductive props also don't nest nicely with liftp.
inductive S.WF : S.Raw → Prop where
  | mk node :
    (wf : T.WF node) →
    (h : node.liftp S.WF) →
    WF (S.Raw.mk node)
-/

-- Here we need an inductive predicate through T.Raw.Forall

inductive Expr.WF : Expr.Raw → Prop where
  | leaf : Expr.WF .leaf
  | app f es :
    (wf_f : Expr.WF f) →
    (wf_es : T.WF es) →
    (wf_es' : es.Forall Expr.WF) →
    WF (Expr.Raw.app f es)

theorem Expr.WF.app_proj1 (h : Expr.WF (Expr.Raw.app f es)) : Expr.WF f :=
  match h with
  | Expr.WF.app _ _ h _ _ => h

theorem Expr.WF.app_proj2 (h : Expr.WF (Expr.Raw.app f es)) : T.WF es :=
  match h with
  | Expr.WF.app _ _ _ h _ => h

theorem Expr.WF.app_proj3 (h : Expr.WF (Expr.Raw.app f es)) : es.Forall Expr.WF :=
  match h with
  | Expr.WF.app _ _ _ _ h => h

def Expr := Subtype Expr.WF

instance instBEqExpr : BEq Expr where
  beq e₁ e₂ := e₁.val == e₂.val

-- Fake constructor
noncomputable def Expr.leaf : Expr where
  val := .leaf
  property := Expr.WF.leaf

noncomputable def Expr.app (f : Expr) (es : T Expr) : Expr where
  val := Expr.Raw.app f.val (es.repr.map Subtype.val)
  property := by
    constructor
    · exact f.property
    · exact T.Raw.wf_map Subtype.val es.repr (T.wf es)
    · exact es.repr.Forall_map Subtype.val Expr.WF (fun x => x.property)

-- Fake casesOn
noncomputable def Expr.casesOn' (motive : Expr → Sort u)
  (leaf : motive .leaf)
  (app : (f : Expr) →  (es : T Expr) → motive (Expr.app f es))
  (e : Expr) : motive e :=
  match e with
  | ⟨re, hwfe⟩ => by
    match re with
    | Expr.Raw.leaf =>
      apply leaf
    | Expr.Raw.app rf res =>
      unfold Expr.app at app
      specialize app
        ⟨rf, hwfe.app_proj1⟩
        (T.abs (res.attach hwfe.app_proj3) (res.wf_attach hwfe.app_proj2))
      simp only [T.repr_abs] at app
      simp only [T.Raw.map_val_attach] at app
      apply app

theorem heq_of_cast_eq  {α β} {a : α} {a' : β} : ∀ (e : α = β) (_ : cast e a = a'), a ≍ a'
  | rfl, rfl => .rfl

theorem cast_eq_iff_heq : cast e a = a' ↔ a ≍ a' :=
  ⟨heq_of_cast_eq _, fun h => by cases h; rfl⟩

theorem cast_congrArg_mk
  {T : Type w}
  {S : Type v}
  (f : T → S)
  (motive : S → Sort u)
  (g : (node : T) → motive (f node))
  (m n : T) (h : m = n) : cast (congrArg (fun x => motive (f x)) h) (g m) = g n := by
  cases h
  rfl

theorem heq_motive_f_congr
  {T : Type w}
  {S : Type v}
  (f : T → S)
  (motive : S → Sort u)
  (g : (node : T) → motive (f node))
  (m n : T) (h : m = n) : g m ≍ g n := by
  cases h
  rfl

theorem heq_motive_f_congr2
  {α : Type v}
  {β : Type w}
  {γ : Type uu}
  (con : α → β → γ)
  (motive : γ → Sort u)
  (hyp : ∀ x y, motive (con x y))
  (x x' : α)
  (hx : x = x')
  (y y' : β)
  (hy : y = y')
  : hyp x y ≍ hyp x' y' := by
  cases hx
  cases hy
  rfl

theorem Expr.casesOn'_eq2 motive leaf app f es :
    Expr.casesOn' motive leaf app (Expr.app f es) = app f es := by
  unfold Expr.casesOn' Expr.app
  simp only [eq_mp_eq_cast, cast_cast, cast_eq_iff_heq]
  apply heq_motive_f_congr2
  · rfl
  · simp [T.Raw.attach_map_val, T.abs_repr]


/-
-- Fake recursor
noncomputable def S.rec' (motive : S → Sort u)
  (mk : (node : T S) → (h : node.below motive) → motive (S.mk node))
  (s : S) : motive s :=
  sorry
-/
