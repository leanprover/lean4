import Std

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

theorem List.join_data [PropSplit α β P] (xs : List α) :
    List.join (List.data xs) (List.prop xs) = xs := by
  induction xs
  · rfl
  · simp_all [List.data, List.join, PropSplit.join_split]


instance [PropSplit α β P] : PropSplit (List α) (List β) (List.Forall P) where
  data := List.data
  prop := List.prop
  join := List.join
  split_join xs hs := by
    induction xs
    · rfl
    · simp_all [List.data, List.join, PropSplit.split_join]
  join_split := List.join_data

-- Trivial Instance for pure data

instance (priority := low) instPropSplitDefault : PropSplit α α (fun _ => True) where
  data x := x
  prop _ := True.intro
  join x _ := x
  split_join _ _ := rfl
  join_split _ := rfl



-- Simple Instance for subtypes

@[reducible]
def instSubtypeSimple {P : α → Prop} : PropSplit (Subtype P) α P where
  data := Subtype.val
  prop := Subtype.property
  join := Subtype.mk
  split_join _ _ := rfl
  join_split _ := rfl

-- Not so simple instance for subtypes
-- (TODO: This probably does not actually work with nested propositions, due to the
-- existential around `P`)

instance {Q : α → Prop} [PropSplit α β P] :
    PropSplit (Subtype Q) β (fun y => ∃ (h : P y), Q (PropSplit.join y h)) where
  data x := PropSplit.data x.val
  prop x := ⟨PropSplit.prop x.val, (PropSplit.join_split x.val).symm ▸ x.property⟩
  join x h := Subtype.mk (PropSplit.join x h.1) (h.2)
  split_join _ _ := by simp [PropSplit.split_join]
  join_split _ := by simp [PropSplit.join_split]

axiom T.WF [BEq α] : T.Raw α → Prop
inductive T.Raw.Forall [BEq α] (p : α → Prop) : T.Raw α → Prop
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

theorem heq_motive_f_congr1_2
  {α1 : Type v1}
  {γ : Type uu}
  (con : α1 → γ)
  {hyp1 : α1 → Sort u1}
  (motive : γ → Sort u3)
  (hyp : ∀ x1 (_h1 : hyp1 x1),  motive (con x1))
  (x1 x1' : α1) (hx1 : x1 = x1')
  (h1 : hyp1 x1) (h1' : hyp1 x1') (hh1 : h1 ≍ h1')
  : hyp x1 h1 ≍ hyp x1' h1' := by
  cases hx1
  cases hh1
  rfl

theorem heq_motive_f_congr2_2
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

theorem heq_motive_f_congr1_1_1
  {α1 : Sort v1}
  {α2 : α1 → Sort v2}
  {γ : Type uu}
  (con : (x : α1) → α2 x → γ)
  {ih : (x : α1) → α2 x → Sort u1}
  (motive : γ → Sort u3)
  (hyp : ∀ x1 x2 (_h1 : ih x1 x2), motive (con x1 x2))
  (x1 x1' : α1) (hx1 : x1 = x1')
  (x2 : α2 x1) (x2' : α2 x1') (hx2 : x2 ≍ x2')
  (h1 : ih x1 x2) (h1' : ih x1' x2') (hh1 : h1 ≍ h1')
  : hyp x1 x2 h1 ≍ hyp x1' x2' h1' := by
  cases hx1
  cases hx2
  cases hh1
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
              (ih1 _)
              (ih2 _))
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
            (ih1 _)
            (ih2 _))
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
  apply heq_motive_f_congr2_2
  · exact PropSplit.join_split f
  · exact PropSplit.join_split es
  · rfl
  · simp only [heq_cast_iff_heq, heq_eq_eq]

end rec

-- New experiment: Vectors

/--
error: (kernel) invalid nested inductive datatype 'Eq', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive VTree' : (n : Nat) → Type u where
  | node : Vector (VTree' n) (n - 1) → VTree' n

/--
error: (kernel) invalid nested inductive datatype 'Eq', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive VTree'' : Type u where
  | node : Vector VTree'' 3 → VTree''

@[simp] theorem List.length_join [PropSplit α β P] (xs : List β) (h : List.Forall P xs) :
    List.length (List.join (α := α) xs h) = xs.length  := by
  induction xs <;> grind [List.join]

structure Vector.Raw (α : Type u) : Type u where
  toList : List α

inductive Vector.Prop (P : α → Prop) : (n : Nat) → (xs : Vector.Raw α) → Prop where
  | mk : (length : xs.length = n) → (prop : List.Forall P xs) → Vector.Prop P n (Vector.Raw.mk xs)

def Vector.ofList {α : Type u} {n : Nat} (xs : List α) (h : xs.length = n) : Vector α n :=
  Vector.mk (List.toArray xs) (by simpa [PropSplit.join] using h)

@[simp] theorem Vector.ofList_toList : Vector.ofList (Vector.toList x) h = x := by
  simp [Vector.ofList]
  rw [← @Vector.toList_toArray]

@[simp] theorem Vector.toList_ofList {α : Type u} {n : Nat} (xs : List α)
  (h : xs.length = n) :
    Vector.toList (Vector.ofList xs h) = xs := by
  simp [Vector.ofList]

instance [PropSplit α β P] :
    PropSplit (Vector α n) (Vector.Raw β) (Vector.Prop P n) where
  data v := Vector.Raw.mk (PropSplit.data v.toList)
  prop v := Vector.Prop.mk ((List.length_map _).symm ▸ v.length_toList) (PropSplit.prop v.toList)
  join xs h := match xs with
    | .mk xs => Vector.ofList
      (PropSplit.join xs (match h with | .mk _ h' => h'))
      (by match h with | .mk h' _ => simpa [PropSplit.join] using h')
  split_join x h := match x with
    | .mk x => by simpa using PropSplit.split_join x _
  join_split x := by
    have := PropSplit.join_split x.toList
    simp [this]

inductive VTree.Raw : Type u where
  | node (cs : Vector.Raw VTree.Raw) : VTree.Raw

-- We cannot do the variant where n is decreasing
-- (local varibles in paramter restriction)
-- but we can do this
inductive VTree.WF : VTree.Raw → Prop where
  | node {cs} (h : Vector.Prop VTree.WF 3 cs) : VTree.WF (VTree.Raw.node cs)

def VTree := Subtype VTree.WF

instance : PropSplit VTree VTree.Raw VTree.WF := instSubtypeSimple

-- fake constructor

def VTree.node (cs : Vector VTree 3) : VTree where
  val := VTree.Raw.node (PropSplit.data cs)
  property := VTree.WF.node (PropSplit.prop cs)

/--
info: recursor VTree.Raw.rec.{u_1, u} : {motive_1 : VTree.Raw → Sort u_1} →
  {motive_2 : Vector.Raw VTree.Raw → Sort u_1} →
    {motive_3 : List VTree.Raw → Sort u_1} →
      ((cs : Vector.Raw VTree.Raw) → motive_2 cs → motive_1 (VTree.Raw.node cs)) →
        ((toList : List VTree.Raw) → motive_3 toList → motive_2 { toList := toList }) →
          motive_3 [] →
            ((head : VTree.Raw) → (tail : List VTree.Raw) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
              (t : VTree.Raw) → motive_1 t
-/
#guard_msgs in
#print VTree.Raw.rec

section rec

variable
  {motive_1 : VTree → Sort u}
  {motive_2 : Vector VTree 3 → Sort u}
  {motive_3 : List VTree → Sort u}
  (node : (cs : Vector VTree 3) → motive_2 cs → motive_1 (VTree.node cs))
  (toList : (xs : List VTree) → (h : xs.length = 3) → motive_3 xs → motive_2 (Vector.ofList xs h))
  (nil : motive_3 [])
  (cons : (head : VTree) → (tail : List VTree) → motive_1 head → motive_3 tail → motive_3 (head :: tail))

noncomputable def VTree.rec' : (t : VTree) → motive_1 t :=
  let go : (x : VTree.Raw) → (h : VTree.WF x) → motive_1 (PropSplit.join x h) :=
    @VTree.Raw.rec
      (fun x => ∀ h, motive_1 (PropSplit.join x h))
      (fun x => ∀ h, motive_2 (PropSplit.join x h))
      (fun x => ∀ h, motive_3 (PropSplit.join x h))
      (fun cs ih h => by
        simpa [VTree.node, PropSplit.split_join] using
          node (PropSplit.join cs (match h with | VTree.WF.node h => h)) (ih _))
      (fun xs ih h =>
        toList (PropSplit.join xs (match h with | .mk _ h => h))
          (by simpa [PropSplit.join] using (match h with | .mk h _ => h))
          (ih _)
      )
      (fun h => nil)
      (fun head tail ih1 ih2 h =>
        cons
          (PropSplit.join head (match h with | List.Forall.cons h _ => h))
          (PropSplit.join tail (match h with | List.Forall.cons _ h => h))
          (ih1 _)
          (ih2 _))
  fun t => go (PropSplit.data t)  (PropSplit.prop t)

noncomputable def VTree.rec_1' : (t : Vector VTree 3) → motive_2 t :=
  let go : (x : Vector.Raw VTree.Raw) → (h : Vector.Prop VTree.WF 3 x) → motive_2 (PropSplit.join x h) :=
    @VTree.Raw.rec_1
      (fun x => ∀ h, motive_1 (PropSplit.join x h))
      (fun x => ∀ h, motive_2 (PropSplit.join x h))
      (fun x => ∀ h, motive_3 (PropSplit.join x h))
      (fun cs ih h => by
        simpa [VTree.node, PropSplit.split_join] using
          node (PropSplit.join cs (match h with | VTree.WF.node h => h)) (ih _))
      (fun xs ih h =>
        toList (PropSplit.join xs (match h with | .mk _ h => h))
          (by simpa [PropSplit.join] using (match h with | .mk h _ => h))
          (ih _)
      )
      (fun h => nil)
      (fun head tail ih1 ih2 h =>
        cons
          (PropSplit.join head (match h with | List.Forall.cons h _ => h))
          (PropSplit.join tail (match h with | List.Forall.cons _ h => h))
          (ih1 _)
          (ih2 _))
  fun t => by
    simpa [PropSplit.join_split] using go (PropSplit.data t) (PropSplit.prop t)

noncomputable def VTree.rec_2' : (t : List VTree) → motive_3 t :=
  let go : (x : List VTree.Raw) → (h : List.Forall VTree.WF x) → motive_3 (PropSplit.join x h) :=
    @VTree.Raw.rec_2
      (fun x => ∀ h, motive_1 (PropSplit.join x h))
      (fun x => ∀ h, motive_2 (PropSplit.join x h))
      (fun x => ∀ h, motive_3 (PropSplit.join x h))
      (fun cs ih h => by
        simpa [VTree.node, PropSplit.split_join] using
          node (PropSplit.join cs (match h with | VTree.WF.node h => h)) (ih _))
      (fun xs ih h =>
        toList (PropSplit.join xs (match h with | .mk _ h => h))
          (by simpa [PropSplit.join] using (match h with | .mk h _ => h))
          (ih _)
      )
      (fun h => nil)
      (fun head tail ih1 ih2 h =>
        cons
          (PropSplit.join head (match h with | List.Forall.cons h _ => h))
          (PropSplit.join tail (match h with | List.Forall.cons _ h => h))
          (ih1 _)
          (ih2 _))
  fun t => by
    simpa [PropSplit.join_split] using go (PropSplit.data t) (PropSplit.prop t)

theorem VTree.rec'_eq1 :
    VTree.rec' node toList nil cons (.node xs) =
      node xs (VTree.rec_1' node toList nil cons xs) := by
  unfold VTree.rec' VTree.rec_1' VTree.node
  simp [PropSplit.data]
  simp only [cast_eq_iff_heq]
  apply heq_motive_f_congr1_2
  · exact PropSplit.join_split xs
  · simp only [heq_cast_iff_heq, heq_eq_eq]

theorem HEq_Prop
  (p : Prop) (q : Prop) (h1 : p) (h2 : q) (_h : p = q) : h1 ≍ h2 := by simp [*]

theorem VTree.rec_1'_eq1 :
    VTree.rec_1' node toList nil cons (.ofList xs h) =
      toList xs h (VTree.rec_2' node toList nil cons xs) := by
  unfold VTree.rec_1' VTree.rec_2'
  simp only [eq_mp_eq_cast, cast_eq_iff_heq]
  apply heq_motive_f_congr1_1_1
        (α2 := fun xs => xs.length = 3)
        (ih := fun x _ => motive_3 x)
  · exact PropSplit.join_split xs
  · apply HEq_Prop
    congr
    simp [PropSplit.join, PropSplit.data, List.join_data, Vector.toList_ofList]
  · simp only [heq_cast_iff_heq]
    rfl

theorem VTree.rec_2'_eq1 :
    VTree.rec_2' node toList nil cons .nil = nil := by rfl


theorem VTree.rec_2'_eq2 :
    VTree.rec_2' node toList nil cons (.cons x xs) =
      cons x xs (VTree.rec' node toList nil cons x) (VTree.rec_2' node toList nil cons xs) := by
  unfold VTree.rec_2' VTree.rec'
  simp only [eq_mp_eq_cast, cast_eq_iff_heq]
  apply heq_motive_f_congr2_2
  · exact PropSplit.join_split _
  · exact PropSplit.join_split _
  · rfl
  · simp [heq_cast_iff_heq]
    rfl

end rec

-- Now trying DTreeMap.

-- The dependent case is too hard. If `β` depends on `α` we cannot reasonable
-- erase `α`. We can probably support erasing `β` only if it is dependent.

-- #print Std.DTreeMap.Internal.Impl

-- Like Std.DTreeMap.Raw but without the ord constraint
structure Std.TreeMap.Raw' α β where
  inner : Std.DTreeMap.Internal.Impl α (fun _ => β)

inductive Std.DTreeMap.Internal.Impl.Prop {α : Type u} {β : Type v} (P₁ : α → Prop) (P₂ : β → Prop) :
    (x : Std.DTreeMap.Internal.Impl α (fun _ => β)) → Prop where
  | inner (size : Nat) (k : α) (v : β) (l r : Impl α (fun _ => β)) :
    P₁ k → P₂ v → Impl.Prop P₁ P₂ l → Impl.Prop P₁ P₂ r →
    Impl.Prop P₁ P₂ (Impl.inner size k v l r)
  | leaf :
    Impl.Prop P₁ P₂ Impl.leaf


inductive Std.TreeMap.Prop {α : Type u} {β : Type v} [Ord α] (P₁ : α → Prop) (P₂ : β → Prop) :
    (x : Std.TreeMap.Raw' α β) → Prop where
  | mk {inner : Std.DTreeMap.Internal.Impl α (fun _ => β)}
       (wf : Std.DTreeMap.Internal.Impl.WF inner)
       (pinner : Std.DTreeMap.Internal.Impl.Prop P₁ P₂ inner)
    : Std.TreeMap.Prop P₁ P₂ (Std.TreeMap.Raw'.mk inner)

def Std.DTreeMap.Internal.Impl.data
  (P₁ : α' → Prop) (P₂ : β' → Prop)
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  : Std.DTreeMap.Internal.Impl α (fun _ => β) → Std.DTreeMap.Internal.Impl α' (fun _ => β')
  | .inner size k v l r =>
    Std.DTreeMap.Internal.Impl.inner
      size (PropSplit.data k) (PropSplit.data v)
      (Std.DTreeMap.Internal.Impl.data P₁ P₂ l)
      (Std.DTreeMap.Internal.Impl.data P₁ P₂ r)
  | .leaf =>
    Std.DTreeMap.Internal.Impl.leaf

-- TODO: This is where we need the preservation of WF by order-preserving `PropSplit.data`
theorem Std.DTreeMap.Internal.Impl.wf_data
  [Ord α]
  [Ord α']
  (P₁ : α' → Prop) (P₂ : β' → Prop)
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  (x : Std.DTreeMap.Internal.Impl α (fun _ => β))
  (wf : Std.DTreeMap.Internal.Impl.WF x) :
  (Std.DTreeMap.Internal.Impl.data P₁ P₂ x).WF := sorry

def Std.DTreeMap.Internal.Impl.prop
  (P₁ : α' → Prop) (P₂ : β' → Prop)
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  : (x : Std.DTreeMap.Internal.Impl α (fun _ => β)) → Std.DTreeMap.Internal.Impl.Prop P₁ P₂ (x.data P₁ P₂)
  | .inner size k v l r =>
    Std.DTreeMap.Internal.Impl.Prop.inner
      size
      (PropSplit.data k) (PropSplit.data v)
      (Std.DTreeMap.Internal.Impl.data P₁ P₂ l)
      (Std.DTreeMap.Internal.Impl.data P₁ P₂ r)
      (PropSplit.prop k) (PropSplit.prop v)
      (Std.DTreeMap.Internal.Impl.prop P₁ P₂ l)
      (Std.DTreeMap.Internal.Impl.prop P₁ P₂ r)
  | .leaf =>
    .leaf

def Std.DTreeMap.Internal.Impl.join
  (P₁ : α' → Prop) (P₂ : β' → Prop)
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  : (x : Std.DTreeMap.Internal.Impl α' (fun _ => β')) →
    Std.DTreeMap.Internal.Impl.Prop P₁ P₂ x →
    Std.DTreeMap.Internal.Impl α (fun _ => β)
  | .inner size k v l r, h =>
    Std.DTreeMap.Internal.Impl.inner
      size
      (PropSplit.join k (match h with | .inner _ _ _ _ _ h _ _ _ => h))
      (PropSplit.join v (match h with | .inner _ _ _ _ _ _ h _ _ => h))
      (Std.DTreeMap.Internal.Impl.join P₁ P₂ l (match h with | .inner _ _ _ _ _ _ _ h _ => h))
      (Std.DTreeMap.Internal.Impl.join P₁ P₂ r (match h with | .inner _ _ _ _ _ _ _ _ h => h))
  | .leaf, _ =>
    Std.DTreeMap.Internal.Impl.leaf

-- TODO: This is where we need the preservation of WF by order-preserving `PropSplit.data`
theorem Std.DTreeMap.Internal.Impl.wf_join
  [Ord α]
  [Ord α']
  (P₁ : α' → Prop) (P₂ : β' → Prop)
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  (x : Std.DTreeMap.Internal.Impl α' (fun _ => β'))
  (h : Std.DTreeMap.Internal.Impl.Prop P₁ P₂ x)
  (wf : Std.DTreeMap.Internal.Impl.WF x) :
  (Std.DTreeMap.Internal.Impl.join (α := α) (β := β) P₁ P₂ x h).WF := sorry

theorem Std.DTreeMap.Internal.Impl.split_join
  [Ord α']
  (P₁ : α' → Prop) (P₂ : β' → Prop)
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  :
  (x : Std.DTreeMap.Internal.Impl α' (fun _ => β')) →
  (h : Std.DTreeMap.Internal.Impl.Prop P₁ P₂ x) →
  (Std.DTreeMap.Internal.Impl.join (α := α) (β := β) P₁ P₂ x h).data P₁ P₂ = x
  | .inner size k v l r, h =>
    by
      simp only [Std.DTreeMap.Internal.Impl.join, Std.DTreeMap.Internal.Impl.data]
      congr
      all_goals simp [PropSplit.split_join, Std.DTreeMap.Internal.Impl.split_join]
  | .leaf, _ => rfl

theorem Std.DTreeMap.Internal.Impl.join_split
  [Ord α']
  (P₁ : α' → Prop) (P₂ : β' → Prop)
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  :
  (x : Std.DTreeMap.Internal.Impl α (fun _ => β)) →
  Std.DTreeMap.Internal.Impl.join (α := α) (β := β) P₁ P₂ (x.data P₁ P₂) (x.prop P₁ P₂) = x
  | .inner size k v l r =>
    by
      simp only [Std.DTreeMap.Internal.Impl.join, Std.DTreeMap.Internal.Impl.data]
      congr
      all_goals simp [PropSplit.join_split, Std.DTreeMap.Internal.Impl.join_split]
  | .leaf => rfl

instance [Ord α']
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  : PropSplit
    (Std.DTreeMap.Internal.Impl α (fun _ => β))
    (Std.DTreeMap.Internal.Impl α' (fun _ => β'))
    (Std.DTreeMap.Internal.Impl.Prop P₁ P₂) where
  data x := x.data P₁ P₂
  prop x := x.prop P₁ P₂
  join x h := x.join P₁ P₂ h
  split_join := Std.DTreeMap.Internal.Impl.split_join _ _
  join_split := Std.DTreeMap.Internal.Impl.join_split _ _

instance [Ord α']
  [PropSplit α α' P₁]
  [PropSplit β β' P₂]
  : PropSplit
    (Std.TreeMap α β cmp)
    (Std.TreeMap.Raw' α' β')
    (Std.TreeMap.Prop P₁ P₂) where
  data x := Std.TreeMap.Raw'.mk (PropSplit.data x.inner.inner)
  prop x := Std.TreeMap.Prop.mk
    (letI : Ord α := ⟨cmp⟩; Std.DTreeMap.Internal.Impl.wf_data _ _ _ x.inner.wf)
    (PropSplit.prop x.inner.inner)
  join x h := match x with
    | .mk x => Std.TreeMap.mk (Std.DTreeMap.mk (PropSplit.join x (match h with | .mk _ h => h)) (letI : Ord α := ⟨cmp⟩; Std.DTreeMap.Internal.Impl.wf_join _ _ _ (match h with | .mk _ h => h) (match h with | .mk h _ => h) ))
  split_join x h := by simp [PropSplit.split_join]
  join_split x := by simp [PropSplit.join_split]

-- Now let's use it

inductive SExpr.Raw where
  | leaf : SExpr.Raw
  | app : SExpr.Raw → Std.TreeMap.Raw' SExpr.Raw Unit → SExpr.Raw

instance : Ord SExpr.Raw where
  compare _ _ := .eq -- TODO: We don't have Ord on Std.TreeMap, so little hope to derive it on SExpr?

attribute [pp_nodot] SExpr.Raw.app

inductive SExpr.WF : SExpr.Raw → Prop where
  | leaf : SExpr.WF .leaf
  | app {f es} :
    (wf_f : SExpr.WF f) →
    (wf_es : Std.TreeMap.Prop SExpr.WF (fun _ => True) es) →
    WF (.app f es)

def SExpr := Subtype SExpr.WF

instance : PropSplit SExpr SExpr.Raw SExpr.WF where
  data := Subtype.val
  prop := Subtype.property
  join x h := ⟨x, h⟩
  split_join _ _ := rfl
  join_split _ := rfl

instance instOrdSExpr : Ord SExpr where
  compare e₁ e₂ := compare e₁.val e₂.val

-- Fake constructor
noncomputable def SExpr.leaf : SExpr where
  val := .leaf
  property := SExpr.WF.leaf

noncomputable def SExpr.app (f : SExpr) (es : Std.TreeMap SExpr Unit) : SExpr where
  val := SExpr.Raw.app (PropSplit.data f) (PropSplit.data es)
  property := SExpr.WF.app (PropSplit.prop f) (PropSplit.prop es)

-- Fake recursor

section rec

/--
info: recursor SExpr.Raw.rec.{u} : {motive_1 : SExpr.Raw → Sort u} →
  {motive_2 : Std.TreeMap.Raw' SExpr.Raw Unit → Sort u} →
    {motive_3 : (Std.DTreeMap.Internal.Impl SExpr.Raw fun x => Unit) → Sort u} →
      motive_1 SExpr.Raw.leaf →
        ((a : SExpr.Raw) →
            (a_1 : Std.TreeMap.Raw' SExpr.Raw Unit) → motive_1 a → motive_2 a_1 → motive_1 (SExpr.Raw.app a a_1)) →
          ((inner : Std.DTreeMap.Internal.Impl SExpr.Raw fun x => Unit) →
              motive_3 inner → motive_2 { inner := inner }) →
            ((size : Nat) →
                (k : SExpr.Raw) →
                  (v : (fun x => Unit) k) →
                    (l r : Std.DTreeMap.Internal.Impl SExpr.Raw fun x => Unit) →
                      motive_1 k → motive_3 l → motive_3 r → motive_3 (Std.DTreeMap.Internal.Impl.inner size k v l r)) →
              motive_3 Std.DTreeMap.Internal.Impl.leaf → (t : SExpr.Raw) → motive_1 t
-/
#guard_msgs in
#print SExpr.Raw.rec

variable
  {motive_1 : SExpr → Sort u}
  {motive_2 : Std.TreeMap SExpr Unit → Sort u}
  {motive_3 : Std.DTreeMap.Internal.Impl SExpr (fun _ => Unit) → Sort u}
  (leaf : motive_1 SExpr.leaf)
  (app : (a : SExpr) → (a_1 : Std.TreeMap SExpr Unit) → motive_1 a → motive_2 a_1 → motive_1 (SExpr.app a a_1))
  (mk : (inner : Std.DTreeMap.Internal.Impl SExpr (fun _ => Unit)) → (h : Std.DTreeMap.Internal.Impl.WF inner) → motive_3 inner →
    motive_2 (.mk (.mk inner h)))
  (node : (size : Nat) → (k : SExpr) → (v : Unit) →
    (l r : Std.DTreeMap.Internal.Impl SExpr (fun _ => Unit)) →
    motive_1 k → motive_3 l → motive_3 r → motive_3 (Std.DTreeMap.Internal.Impl.inner size k v l r))
  (tleaf : motive_3 Std.DTreeMap.Internal.Impl.leaf)

noncomputable def SExpr.rec' : (t : SExpr) → motive_1 t :=
  let go : (x : SExpr.Raw) → (h : SExpr.WF x) → motive_1 (PropSplit.join x h) :=
    @SExpr.Raw.rec
      (fun x => ∀ h, motive_1 (PropSplit.join x h))
      (fun x => ∀ h, motive_2 (PropSplit.join x h))
      (fun x => ∀ (h : Std.DTreeMap.Internal.Impl.Prop _ _ x), motive_3 (PropSplit.join x h))
      (fun h => leaf)
      (fun f es ih1 ih2 h => by
        simpa [SExpr.app, PropSplit.split_join] using
          app (PropSplit.join f (match h with | SExpr.WF.app h _ => h))
              (PropSplit.join es (match h with | SExpr.WF.app _ h => h))
              (ih1 (match h with | SExpr.WF.app h _ => h))
              (ih2 (match h with | SExpr.WF.app _ h => h)))
      (fun inner ih h => by
        simpa [PropSplit.split_join] using
          mk
            (PropSplit.join inner (match h with | .mk _ h => h))
            _
            (ih _)
      )
      (fun size k v l r pk pl pr h => by
        simpa [PropSplit.split_join] using
          node size
            (PropSplit.join k (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ h _ _ _ => h))
            v
            (PropSplit.join l (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ _ _ h _ => h))
            (PropSplit.join r (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ _ _ _ h => h))
            (pk _)
            (pl _)
            (pr _))
      (fun h => tleaf)
  fun x => by simpa [PropSplit.join_split] using go (PropSplit.data x) (PropSplit.prop x)

noncomputable def SExpr.rec_1' : (x : Std.TreeMap SExpr Unit) → motive_2 x :=
  let go : (x : Std.TreeMap.Raw' SExpr.Raw Unit) → (h : _) → motive_2 (PropSplit.join x h) :=
    @SExpr.Raw.rec_1
      (fun x => ∀ h, motive_1 (PropSplit.join x h))
      (fun x => ∀ h, motive_2 (PropSplit.join x h))
      (fun x => ∀ (h : Std.DTreeMap.Internal.Impl.Prop _ _ x), motive_3 (PropSplit.join x h))
      (fun h => leaf)
      (fun f es ih1 ih2 h => by
        simpa [SExpr.app, PropSplit.split_join] using
          app (PropSplit.join f (match h with | SExpr.WF.app h _ => h))
              (PropSplit.join es (match h with | SExpr.WF.app _ h => h))
              (ih1 (match h with | SExpr.WF.app h _ => h))
              (ih2 (match h with | SExpr.WF.app _ h => h)))
      (fun inner ih h => by
        simpa [PropSplit.split_join] using
          mk
            (PropSplit.join inner (match h with | .mk _ h => h))
            _
            (ih _)
      )
      (fun size k v l r pk pl pr h => by
        simpa [PropSplit.split_join] using
          node size
            (PropSplit.join k (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ h _ _ _ => h))
            v
            (PropSplit.join l (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ _ _ h _ => h))
            (PropSplit.join r (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ _ _ _ h => h))
            (pk _)
            (pl _)
            (pr _))
      (fun h => tleaf)
  fun x => by simpa [PropSplit.join_split] using go (PropSplit.data x) (PropSplit.prop x)

noncomputable def SExpr.rec_2' : (x : _) → motive_3 x :=
  let go : (x : _) → (h : _) → motive_3 (PropSplit.join x h) :=
    @SExpr.Raw.rec_2
      (fun x => ∀ h, motive_1 (PropSplit.join x h))
      (fun x => ∀ h, motive_2 (PropSplit.join x h))
      (fun x => ∀ (h : Std.DTreeMap.Internal.Impl.Prop _ _ x), motive_3 (PropSplit.join x h))
      (fun h => leaf)
      (fun f es ih1 ih2 h => by
        simpa [SExpr.app, PropSplit.split_join] using
          app (PropSplit.join f (match h with | SExpr.WF.app h _ => h))
              (PropSplit.join es (match h with | SExpr.WF.app _ h => h))
              (ih1 (match h with | SExpr.WF.app h _ => h))
              (ih2 (match h with | SExpr.WF.app _ h => h)))
      (fun inner ih h => by
        simpa [PropSplit.split_join] using
          mk
            (PropSplit.join inner (match h with | .mk _ h => h))
            _
            (ih _)
      )
      (fun size k v l r pk pl pr h => by
        simpa [PropSplit.split_join] using
          node size
            (PropSplit.join k (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ h _ _ _ => h))
            v
            (PropSplit.join l (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ _ _ h _ => h))
            (PropSplit.join r (match h with | Std.DTreeMap.Internal.Impl.Prop.inner _ _ _ _ _ _ _ _ h => h))
            (pk _)
            (pl _)
            (pr _))
      (fun h => tleaf)
  fun x => by simpa [PropSplit.join_split] using go (PropSplit.data x) (PropSplit.prop x)

theorem SExpr.rec'_eq1 :
    SExpr.rec' leaf app mk node tleaf SExpr.leaf = leaf := by
  rfl

theorem SExpr.rec'_eq2 :
    SExpr.rec' leaf app mk node tleaf (SExpr.app f es) =
      app f es (SExpr.rec' leaf app mk node tleaf f)
               (SExpr.rec_1' leaf app mk node tleaf es)
      := by
  unfold SExpr.rec' SExpr.rec_1' SExpr.app
  simp [PropSplit.data]
  simp only [cast_eq_iff_heq]
  apply heq_motive_f_congr2_2
  · exact PropSplit.join_split f
  · exact PropSplit.join_split es
  · rfl
  · simp only [heq_cast_iff_heq, heq_eq_eq]

theorem SExpr.rec_1'_eq1 :
    SExpr.rec_1' leaf app mk node tleaf (.mk (.mk inner h)) =
      mk inner h
        (SExpr.rec_2' leaf app mk node tleaf inner)
      := by
  unfold SExpr.rec_1' SExpr.rec_2'
  simp [PropSplit.data]
  simp only [cast_eq_iff_heq]
  apply heq_motive_f_congr1_1_1
    (ih := fun x _ => motive_3 x)
  · exact PropSplit.join_split inner
  · apply HEq_Prop
    congr
    simp [PropSplit.join, Std.DTreeMap.Internal.Impl.join_split]
  · simp only [heq_cast_iff_heq]
    rfl
