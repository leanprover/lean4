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

-- Trivial Instance for pure data

-- instance (priority := low) instPropSplitDefault : PropSplit α α (fun _ => True) where
--   data x := x
--   prop _ := True.intro
--   join x _ := x
--   split_join _ _ := rfl
--   join_split _ := rfl



-- Simple Instance for subtypes

-- instance {P : α → Prop} : PropSplit (Subtype P) α P where
--   data := Subtype.val
--   prop := Subtype.property
--   join := Subtype.mk
--   split_join _ _ := rfl
--   join_split _ := rfl

-- Not so simple instance for subtypes

instance {Q : α → Prop} [PropSplit α β P] :
    PropSplit (Subtype Q) β (fun y => ∃ (h : P y), Q (PropSplit.join y h)) where
  data x := PropSplit.data x.val
  prop x := ⟨PropSplit.prop x.val, (PropSplit.join_split x.val).symm ▸ x.property⟩
  join x h := Subtype.mk (PropSplit.join x h.1) (h.2)
  split_join _ _ := by simp [PropSplit.split_join]
  join_split _ := by simp [PropSplit.join_split]

axiom T.WF [BEq α] : T.Raw α → Prop
inductive T.Raw.Forall (p : α → Prop) : T.Raw α → Prop
  | mk x xs : p x → xs.Forall p → T.Raw.Forall p (T.Raw.mk x xs)

@[instance]
axiom instPropSplitT [PropSplit α β P] [BEq α] [BEq β] :
  PropSplit (T α) (T.Raw β) (T.Raw.Forall P)


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
  | ⟨re, hwfe⟩ =>
    match re with
    | Expr.Raw.leaf =>
      leaf
    | Expr.Raw.app rf res => by
      specialize app
        (PropSplit.join rf (match hwfe with | Expr.WF.app h _ => h))
        (PropSplit.join res (match hwfe with | Expr.WF.app _ h => h))
      simp only [Expr.app, PropSplit.split_join] at app
      apply app
    | Expr.Raw.nest res => by
      specialize nest
        (PropSplit.join res (match hwfe with | Expr.WF.nest h => h))
      simp only [Expr.nest, PropSplit.split_join] at nest
      apply nest

theorem heq_of_cast_eq  {α β} {a : α} {a' : β} : ∀ (e : α = β) (_ : cast e a = a'), a ≍ a'
  | rfl, rfl => .rfl

theorem cast_eq_iff_heq : cast e a = a' ↔ a ≍ a' :=
  ⟨heq_of_cast_eq _, fun h => by cases h; rfl⟩

@[simp]
theorem heq_cast_iff_heq {α β γ : Sort _} (e : β = γ) (a : α) (b : β) :
    a ≍ cast e b ↔ a ≍ b := by subst e; rfl

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

theorem heq_motive_f_congr2_4
  {α1 : Type v1}
  {α2 : Type v2}
  {γ : Type uu}
  (con : α1 → α2 → γ)
  {hyp1 : α1 → Sort u1}
  {hyp2 : α2 → Sort u2}
  (motive : γ → Sort u3)
  (hyp : ∀ x1 x2 (_h1 : hyp1 x1) (_h2 : hyp2 x2), motive (con x1 x2))
  (x1 x1' : α1) (hx1 : x1 = x1')
  (x2 x2' : α2) (hx2 : x2 = x2')
  (h1 : hyp1 x1) (h1' : hyp1 x1') (hh1 : h1 ≍ h1')
  (h2 : hyp2 x2) (h2' : hyp2 x2') (hh2 : h2 ≍ h2')
  : hyp x1 x2 h1 h2 ≍ hyp x1' x2' h1' h2' := by
  cases hx1
  cases hx2
  cases hh1
  cases hh2
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

axiom T.mk [BEq α] : α → T α → T α -- pseudo-implementation, representative for any kernel-friendly type

section rec

-- We need a sorry that is defeq to itself
axiom uniqeSorry : α

variable
  {motive_1 : Expr → Sort u}
  {motive_2 : T Expr → Sort u}
  {motive_3 : T (List (T Expr)) → Sort u}
  {motive_4 : List (T Expr) → Sort u}
  (leaf : motive_1 Expr.leaf)
  (app : (a : Expr) → (a_1 : T Expr) → motive_1 a → motive_2 a_1 → motive_1 (Expr.app a a_1))
  (nest : (a : T (List (T Expr))) → motive_3 a → motive_1 (Expr.nest a))
  -- (mk1 : (a : Expr) → (a_1 : T Expr) → motive_1 a → motive_2 a_1 → motive_2 (T.mk a a_1))
  -- (mk2 : (a : List (T Expr)) →
  --    (a_1 : T (List (T Expr))) → motive_4 a → motive_3 a_1 → motive_3 (T.mk a a_1))
  (nil : motive_4 [])
  (cons : (head : T Expr) → (tail : List (T Expr)) → motive_2 head → motive_4 tail → motive_4 (head :: tail))

set_option warn.sorry false in
noncomputable def Expr.rec' : (t : Expr) → motive_1 t :=
  let go : (x : Expr.Raw) → (h : Expr.WF x) → motive_1 (PropSplit.join x h) :=
    @Expr.Raw.rec
      (fun x => ∀ h, motive_1 (PropSplit.join x h))
      (fun x => ∀ h, motive_2 (PropSplit.join x h))
      (fun x => ∀ h, motive_3 (PropSplit.join x h))
      (fun x => ∀ h, motive_4 (PropSplit.join x h))
      (fun h => leaf)
      (fun f es ih1 ih2 h => by
        simpa [Expr.app, PropSplit.split_join] using
          app (PropSplit.join f (match h with | Expr.WF.app h _ => h))
              (PropSplit.join es (match h with | Expr.WF.app _ h => h))
              (ih1 (match h with | Expr.WF.app h _ => h))
              (ih2 (match h with | Expr.WF.app _ h => h)))
      (fun es ih h => by
        simpa [Expr.nest, PropSplit.split_join] using
          nest (PropSplit.join es (match h with | Expr.WF.nest h => h))
              (ih (match h with | Expr.WF.nest h => h)))
      -- The sorries here are due to relating T.mk/T.Raw.mk/PropSplit.join,
      -- which is axiomatized
      (fun x xs ih1 ih2 h => uniqeSorry)
      (fun x xs ih1 ih2 h => uniqeSorry)
      (fun h => nil)
      (fun x xs ih1 ih2 h => by
        simpa [PropSplit.split_join] using
          cons
            (PropSplit.join x (match h with | List.Forall.cons h _ => h))
            (PropSplit.join xs (match h with | List.Forall.cons _ h => h))
            (ih1 (match h with | List.Forall.cons h _ => h))
            (ih2 (match h with | List.Forall.cons _ h => h)))
  fun t => go (PropSplit.data t)  (PropSplit.prop t)

set_option warn.sorry false in
noncomputable def Expr.rec_1' : (t : T Expr) → motive_2 t :=
  let go : (x : T.Raw Expr.Raw) → (h : T.Raw.Forall Expr.WF x) → motive_2 (PropSplit.join x h) :=
    @Expr.Raw.rec_1
      (fun x => ∀ h, motive_1 (PropSplit.join x h))
      (fun x => ∀ h, motive_2 (PropSplit.join x h))
      (fun x => ∀ h, motive_3 (PropSplit.join x h))
      (fun x => ∀ h, motive_4 (PropSplit.join x h))
      (fun h => leaf)
      (fun f es ih1 ih2 h => by
        simpa [Expr.app, PropSplit.split_join] using
          app (PropSplit.join f (match h with | Expr.WF.app h _ => h))
              (PropSplit.join es (match h with | Expr.WF.app _ h => h))
              (ih1 (match h with | Expr.WF.app h _ => h))
              (ih2 (match h with | Expr.WF.app _ h => h)))
      (fun es ih h => by
        simpa [Expr.nest, PropSplit.split_join] using
          nest (PropSplit.join es (match h with | Expr.WF.nest h => h))
              (ih (match h with | Expr.WF.nest h => h)))
      -- The sorries here are due to relating T.mk/T.Raw.mk/PropSplit.join,
      -- which is axiomatized
      (fun x xs ih1 ih2 h => uniqeSorry)
      (fun x xs ih1 ih2 h => uniqeSorry)
      (fun h => nil)
      (fun x xs ih1 ih2 h => by
        simpa [PropSplit.split_join] using
          cons
            (PropSplit.join x (match h with | List.Forall.cons h _ => h))
            (PropSplit.join xs (match h with | List.Forall.cons _ h => h))
            (ih1 (match h with | List.Forall.cons h _ => h))
            (ih2 (match h with | List.Forall.cons _ h => h)))
  fun t =>
    by simpa [PropSplit.join_split] using go (PropSplit.data t)  (PropSplit.prop t)

theorem Expr.rec'_eq1 :
    Expr.rec' leaf app nest nil cons Expr.leaf = leaf := by
  rfl

theorem Expr.rec'_eq2 :
    Expr.rec' leaf app nest nil cons (Expr.app f es) =
      app f es (Expr.rec' leaf app nest nil cons f)
               (Expr.rec_1' leaf app nest nil cons es)
      := by
  unfold Expr.rec' Expr.rec_1' Expr.app
  simp [PropSplit.data]
  simp only [cast_eq_iff_heq]
  apply heq_motive_f_congr2_4
  · exact PropSplit.join_split f
  · exact PropSplit.join_split es
  · rfl
  · simp only [heq_cast_iff_heq, heq_eq_eq]
