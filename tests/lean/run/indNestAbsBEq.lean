opaque T : (α : Type u) → [BEq α] → Type u

@[instance] axiom instBeqT [BEq α] : BEq (T α)

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

axiom T.WF [BEq α] : T.Raw α → Prop
axiom T.abs : (x : T.Raw α) → T.WF x → T α
axiom T.repr : T α → T.Raw α
axiom T.wf : (t : T α) → T.WF t.repr
axiom T.abs_repr {x : T α} : T.abs (T.repr x) (T.wf x) = x
axiom T.repr_abs {x : T.Raw α} {h : T.WF x} : T.repr (T.abs x h) = x
axiom T.Raw.map : (f : α → β) → T.Raw α → T.Raw β

-- Cannot be abstract, since we need to define a nested inductive predicate
inductive T.Raw.Forall (p : α → Prop) : T.Raw α → Prop
  | mk x xs : p x → xs.Forall p → T.Raw.Forall p (T.Raw.mk x xs)

axiom T.Raw.Forall.conj : T.Raw.Forall p m → T.Raw.Forall q m → T.Raw.Forall (fun x => p x ∧ q x) m


axiom T.Raw.wf_map (f : α → β) (x : T.Raw α) (h : T.WF x) : T.WF (T.Raw.map f x)
axiom T.Raw.Forall_map {α : Type u} {β : Type v} (f : α → β) (p : β → Prop)
  (m : T.Raw α) (h : ∀ x, p (f x)) :
  T.Raw.Forall p (m.map f)
axiom T.Raw.attach {p : α → Prop} (m : T.Raw α) : T.Raw.Forall p m → T.Raw (Subtype p)
axiom T.Raw.wf_attach (x : T.Raw α) (h1 : T.WF x) {h2 : x.Forall p} : T.WF (x.attach h2)
axiom T.Raw.map_map (x : T.Raw α) (f : α → β) (g : β → γ) :
  T.Raw.map g (T.Raw.map f x) = T.Raw.map (fun x => g (f x)) x
axiom T.Raw.map_val_attach (x : T.Raw α) (h : T.Raw.Forall p x) :
  T.Raw.map Subtype.val (x.attach h) = x
axiom T.Raw.attach_map_val (x : T.Raw (Subtype p)) (h : T.Raw.Forall p (x.map Subtype.val)) :
  (T.Raw.map Subtype.val x).attach h = x


inductive Expr.Raw where
  | leaf : Expr.Raw
  | app : Expr.Raw → T.Raw Expr.Raw → Expr.Raw
  | nest : T.Raw (List (T.Raw Expr.Raw)) → Expr.Raw
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

inductive List.Forall (p : α → Prop) : List α → Prop where
  | nil : List.Forall p []
  | cons : ∀ x xs, p x → xs.Forall p → List.Forall p (x :: xs)

axiom List.Forall_map {α : Type u} {β : Type v} (f : α → β) (p : β → Prop)
  (m : List α) (h : ∀ x, p (f x)) :
  List.Forall p (m.map f)
axiom List.attach' {p : α → Prop} (m : List α) : List.Forall p m → List (Subtype p)
axiom List.Forall.conj : List.Forall p m → List.Forall q m → List.Forall (fun x => p x ∧ q x) m
axiom List.map_val_attach (x : List α) (h : List.Forall p x) : List.map Subtype.val (x.attach' h) = x

inductive Expr.WF : Expr.Raw → Prop where
  | leaf : Expr.WF .leaf
  | app f es :
    (wf_f : Expr.WF f) →
    (wf_es : T.WF es) →
    (wf_es' : es.Forall Expr.WF) →
    WF (Expr.Raw.app f es)
  | nest es :
    (wf_es : T.WF es) →
    (wf_es_forall : es.Forall (fun x => x.Forall (fun x => T.WF x))) →
    (wf_es_forall : es.Forall (fun x => x.Forall (fun x => x.Forall (fun x => Expr.WF x)))) →
    WF (Expr.Raw.nest es)


theorem Expr.WF.app_proj1 (h : Expr.WF (Expr.Raw.app f es)) : Expr.WF f :=
  match h with
  | Expr.WF.app _ _ h _ _ => h

theorem Expr.WF.app_proj2 (h : Expr.WF (Expr.Raw.app f es)) : T.WF es :=
  match h with
  | Expr.WF.app _ _ _ h _ => h

theorem Expr.WF.app_proj3 (h : Expr.WF (Expr.Raw.app f es)) : es.Forall Expr.WF :=
  match h with
  | Expr.WF.app _ _ _ _ h => h

theorem Expr.WF.nest_proj1 (h : Expr.WF (Expr.Raw.nest es)) : T.WF es :=
  match h with
  | Expr.WF.nest _ h _ _ => h

theorem Expr.WF.nest_proj2 (h : Expr.WF (Expr.Raw.nest es)) :  es.Forall (fun x => x.Forall (fun x => T.WF x)) :=
  match h with
  | Expr.WF.nest _ _ h _ => h

theorem Expr.WF.nest_proj3 (h : Expr.WF (Expr.Raw.nest es)) : es.Forall (fun x => x.Forall (fun x => x.Forall (fun x => Expr.WF x))) :=
  match h with
  | Expr.WF.nest _ _ _ h => h

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
    · exact T.Raw.wf_map _ _ (T.wf es)
    · exact es.repr.Forall_map Subtype.val Expr.WF (fun x => x.property)

noncomputable def Expr.nest (es : T (List (T Expr))) : Expr where
  val := Expr.Raw.nest (es.repr.map (·.map (·.repr.map Subtype.val)))
  property := by
    constructor
    · apply T.Raw.wf_map _ _ (T.wf es)
    · apply es.repr.Forall_map
      intro x
      apply List.Forall_map
      intro xs
      apply T.Raw.wf_map
      apply T.wf
    · apply T.Raw.Forall_map
      intro x
      apply List.Forall_map
      intro xs
      apply T.Raw.Forall_map
      intro x
      apply x.property

-- Fake casesOn
noncomputable def Expr.casesOn' (motive : Expr → Sort u)
  (leaf : motive .leaf)
  (app : (f : Expr) → (es : T Expr) → motive (Expr.app f es))
  (nest : (es : T (List (T Expr))) → motive (Expr.nest es))
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
    | Expr.Raw.nest res =>
      unfold Expr.nest at nest
      let res' := res.attach (hwfe.nest_proj2.conj  hwfe.nest_proj3)
      let res' := res'.map (fun x =>(x.1.attach' (x.2.1.conj x.2.2)))
      let res' := res'.map (·.map (fun x => T.abs (x.1.attach x.2.2) (T.Raw.wf_attach _ x.2.1)))
      let res' := T.abs res' sorry
      specialize nest res'
      subst res' res' res' res'
      simp only [T.repr_abs] at nest
      simp only [T.Raw.map_map] at nest
      simp only [List.map_map, Function.comp_def] at nest
      simp only [T.repr_abs] at nest
      simp only [T.Raw.map_val_attach] at nest
      simp only [List.map_val_attach] at nest
      simp only [T.Raw.map_val_attach] at nest
      exact nest

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

axiom T.abs_eq_of (x : T.Raw α) (h : T.WF x) : x = y.repr → T.abs x h = y

axiom T.Raw.Forall.map  : T.Raw.Forall p (m.map f) → T.Raw.Forall (fun x => p (f x)) m
axiom T.Raw.map_attach (x : T.Raw α) (f : α → β) (h : T.Raw.Forall p (x.map f)) :
  (x.map f).attach h = (x.attach (h.map)).map (fun x => ⟨f x.1, x.2⟩)
axiom List.Forall.map  : List.Forall p (m.map f) → List.Forall (fun x => p (f x)) m
axiom List.map_attach' (x : List α) (f : α → β) (h : List.Forall p (x.map f)) :
  (x.map f).attach' h = (x.attach' (h.map)).map (fun x => ⟨f x.1, x.2⟩)

theorem Expr.casesOn'_eq2 motive leaf app nest f es :
    Expr.casesOn' motive leaf app nest (Expr.app f es) = app f es := by
  unfold Expr.casesOn' Expr.app
  simp only [eq_mp_eq_cast, cast_cast, cast_eq_iff_heq]
  apply heq_motive_f_congr2
  · rfl
  · -- apply T.abs_eq_of
    simp only [T.Raw.attach_map_val]
    simp only [T.abs_repr]


theorem Expr.casesOn'_eq3 motive leaf app nest es :
    Expr.casesOn' motive leaf app nest (Expr.nest es) = nest es := by
  unfold Expr.casesOn' Expr.nest
  simp only [eq_mp_eq_cast, cast_cast, id, cast_eq_iff_heq]
  apply heq_motive_f_congr
  · skip
    -- apply T.abs_eq_of
    simp only [T.Raw.map_map]
    simp only [T.Raw.map_attach]
    simp only [T.Raw.map_map]
    simp only [List.map_attach']
    simp only [List.map_map, Function.comp_def]
    simp only [T.Raw.map_attach]


    -- simp [T.Raw.map_map, List.map_map, Function.comp, List.attach_map_val,
      -- T.Raw.attach_map_val, T.abs_repr]

    sorry

/-
-- Fake recursor
noncomputable def S.rec' (motive : S → Sort u)
  (mk : (node : T S) → (h : node.below motive) → motive (S.mk node))
  (s : S) : motive s :=
  sorry
-/
