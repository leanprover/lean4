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

class PropSplit (α : Type u) (β : outParam (Type v)) (P : outParam (β → Prop)) where
  data : α → β
  prop : (x : α) → P (data x)
  join : (x : β) → P x → α
  split_join : ∀ x h, data (join x h) = x
  join_split : ∀ x, join (data x) (prop x) = x

-- Instance for lists

inductive List.Forall (p : α → Prop) : List α → Prop where
  | nil : List.Forall p []
  | cons : ∀ {x xs}, p x → xs.Forall p → List.Forall p (x :: xs)

def List.data [PropSplit α β P] : List α → List β := List.map PropSplit.data

def List.prop [PropSplit α β P] : (xs : List α) → List.Forall P xs.data
  | [] => List.Forall.nil
  | x::xs => List.Forall.cons (PropSplit.prop x) (List.prop xs)

def List.join [PropSplit α β P] : (ys : List β) → Forall P ys → List α
  | [], _ => []
  | x::xs, h => PropSplit.join x (match h with | .cons h _ => h) :: List.join xs (match h with | .cons _ hs => hs)

instance [PropSplit α β P] : PropSplit (List α) (List β) (List.Forall P) where
  data := List.data
  prop := List.prop
  join := List.join
  split_join xs hs := by
    induction xs
    · rfl
    · simp_all [List.data, List.join, PropSplit.split_join]
  join_split xs := by
    induction xs
    · rfl
    · simp_all [List.data, List.join, PropSplit.join_split]

-- Trivial Instance for subtypes

instance {P : α → Prop} : PropSplit (Subtype P) α P where
  data := Subtype.val
  prop := Subtype.property
  join := Subtype.mk
  split_join _ _ := rfl
  join_split _ := rfl

-- Trivial Instance for pure data

-- instance (priority := low) instPropSplitDefault : PropSplit α α (fun _ => True) where
--   data x := x
--   prop _ := True.intro
--   join x _ := x
--   split_join _ _ := rfl
--   join_split _ := rfl

axiom T.WF [BEq α] : T.Raw α → Prop
inductive T.Raw.Forall (p : α → Prop) : T.Raw α → Prop
  | mk x xs : p x → xs.Forall p → T.Raw.Forall p (T.Raw.mk x xs)

@[instance]
axiom instPropSplitT [PropSplit α β P] [BEq α] [BEq β] : PropSplit (T α) (T.Raw β) (T.Raw.Forall P)


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

inductive Expr.WF : Expr.Raw → Prop where
  | leaf : Expr.WF .leaf
  | app {f es} :
    (wf_f : Expr.WF f) →
    (wf_es : T.Raw.Forall Expr.WF es) →
    WF (Expr.Raw.app f es)
  | nest {es} :
    (wf_es : T.Raw.Forall (List.Forall (T.Raw.Forall Expr.WF)) es) →
    WF (Expr.Raw.nest es)

def Expr := Subtype Expr.WF

instance : PropSplit Expr Expr.Raw Expr.WF where
  data := Subtype.val
  prop := Subtype.property
  join x h := ⟨x, h⟩
  split_join _ _ := rfl
  join_split _ := rfl

instance instBEqExpr : BEq Expr where
  beq e₁ e₂ := e₁.val == e₂.val

-- Fake constructor
noncomputable def Expr.leaf : Expr where
  val := .leaf
  property := Expr.WF.leaf

noncomputable def Expr.app (f : Expr) (es : T Expr) : Expr where
  val := Expr.Raw.app (PropSplit.data f) (PropSplit.data es)
  property := Expr.WF.app (PropSplit.prop f) (PropSplit.prop es)

noncomputable def Expr.nest (es : T (List (T Expr))) : Expr where
  val := Expr.Raw.nest (PropSplit.data es)
  property := Expr.WF.nest (PropSplit.prop es)

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
      specialize app
        (PropSplit.join rf (match hwfe with | Expr.WF.app h _ => h))
        (PropSplit.join res (match hwfe with | Expr.WF.app _ h => h))
      simp only [Expr.app, PropSplit.split_join] at app
      apply app
    | Expr.Raw.nest res =>
      specialize nest
        (PropSplit.join res (match hwfe with | Expr.WF.nest h => h))
      simp only [Expr.nest, PropSplit.split_join] at nest
      apply nest

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


theorem Expr.casesOn'_eq1 motive leaf app nest :
    Expr.casesOn' motive leaf app nest .leaf = leaf := by
  rfl

theorem Expr.casesOn'_eq2 motive leaf app nest f es :
    Expr.casesOn' motive leaf app nest (Expr.app f es) = app f es := by
  unfold Expr.casesOn' Expr.app
  simp only [eq_mp_eq_cast, cast_eq_iff_heq]
  apply heq_motive_f_congr2
  · rfl
  · exact PropSplit.join_split es

theorem Expr.casesOn'_eq3 motive leaf app nest es :
    Expr.casesOn' motive leaf app nest (Expr.nest es) = nest es := by
  unfold Expr.casesOn' Expr.nest
  simp only [eq_mp_eq_cast, cast_eq_iff_heq]
  apply heq_motive_f_congr
  · exact PropSplit.join_split es

/-
-- Fake recursor
noncomputable def S.rec' (motive : S → Sort u)
  (mk : (node : T S) → (h : node.below motive) → motive (S.mk node))
  (s : S) : motive s :=
  sorry
-/
