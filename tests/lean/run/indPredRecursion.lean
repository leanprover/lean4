/-!
# Tests for `brecOn` on recursive inductive predicates
-/

/-!
Transitive closure (see issue 1672)
-/

inductive TransClosure (r : α → α → Prop) : α → α → Prop
  | extends : r a b → TransClosure r a b
  | trans_left : r a b → TransClosure r b c → TransClosure r a c

/--
info: TransClosure.brecOn.{u_1} {α : Sort u_1} {r : α → α → Prop} {motive : (a a_1 : α) → TransClosure r a a_1 → Prop}
  {a✝ a✝¹ : α} (t : TransClosure r a✝ a✝¹)
  (F_1 : ∀ (a a_1 : α) (t : TransClosure r a a_1), TransClosure.below t → motive a a_1 t) : motive a✝ a✝¹ t
-/
#guard_msgs in
#check TransClosure.brecOn

theorem TransClosure.recTest (h : TransClosure r a b) : True :=
  match h with
  | .extends _ => trivial
  | .trans_left _ h => h.recTest
termination_by structural h

/-!
Symmetric closure (see issue 4540)
-/

inductive SymmGen (r : α → α → Prop) : α → α → Prop
  | rel : ∀ x y, r x y → SymmGen r x y
  | symm : ∀ x y, SymmGen r x y → SymmGen r y x

/--
info: SymmGen.brecOn.{u_1} {α : Sort u_1} {r : α → α → Prop} {motive : (a a_1 : α) → SymmGen r a a_1 → Prop} {a✝ a✝¹ : α}
  (t : SymmGen r a✝ a✝¹) (F_1 : ∀ (a a_1 : α) (t : SymmGen r a a_1), SymmGen.below t → motive a a_1 t) : motive a✝ a✝¹ t
-/
#guard_msgs in
#check SymmGen.brecOn

theorem SymmGen.recTest (h : SymmGen r a b) : True :=
  match h with
  | .rel _ _ _ => trivial
  | .symm _ _ h => h.recTest
termination_by structural h

/-!
Basic typing relation
-/

inductive Ty : Type where
  | unit : Ty
  | arr  : Ty → Ty → Ty

inductive Term : Type where
  | var : Nat → Term
  | unit : Term
  | abs : Term → Term
  | app : Term → Term → Term

inductive Wt : List Ty → Term → Ty → Prop where
  | var {Γ x} : (h : x < Γ.length) → Wt Γ (.var x) Γ[x]
  | unit {Γ} : Wt Γ .unit .unit
  | abs {Γ b A B} : Wt (A :: Γ) b B → Wt Γ (.abs b) (.arr A B)
  | app {Γ b a A B} : Wt Γ b (.arr A B) → Wt Γ a A → Wt Γ (.app b a) B

/--
info: Wt.brecOn {motive : (a : List Ty) → (a_1 : Term) → (a_2 : Ty) → Wt a a_1 a_2 → Prop} {a✝ : List Ty} {a✝¹ : Term}
  {a✝² : Ty} (t : Wt a✝ a✝¹ a✝²)
  (F_1 : ∀ (a : List Ty) (a_1 : Term) (a_2 : Ty) (t : Wt a a_1 a_2), Wt.below t → motive a a_1 a_2 t) :
  motive a✝ a✝¹ a✝² t
-/
#guard_msgs in
#check Wt.brecOn

theorem Wt.recTest (h : Wt Γ a A) : True :=
  match h with
  | .var _ => trivial
  | .unit => trivial
  | .abs h => h.recTest
  | .app h h' => h.recTest
termination_by structural h

/-!
Mutual inductives
-/

mutual

inductive EvenDist : Nat → Nat → Prop where
  | zero : EvenDist 0 0
  | succ_left (h : Nat → OddDist a b) : EvenDist a.succ b
  | succ_right (h : OddDist a b) : EvenDist a b.succ

inductive OddDist : Nat → Nat → Prop where
  | succ_left (h : EvenDist a b) : OddDist a.succ b
  | succ_right (h : EvenDist a b) : OddDist a b.succ

end

/--
info: EvenDist.brecOn {motive_1 : (a a_1 : Nat) → EvenDist a a_1 → Prop} {motive_2 : (a a_1 : Nat) → OddDist a a_1 → Prop}
  {a✝ a✝¹ : Nat} (t : EvenDist a✝ a✝¹) (F_1 : ∀ (a a_1 : Nat) (t : EvenDist a a_1), t.below → motive_1 a a_1 t)
  (F_2 : ∀ (a a_1 : Nat) (t : OddDist a a_1), t.below → motive_2 a a_1 t) : motive_1 a✝ a✝¹ t
-/
#guard_msgs in
#check EvenDist.brecOn

/--
info: OddDist.brecOn {motive_1 : (a a_1 : Nat) → EvenDist a a_1 → Prop} {motive_2 : (a a_1 : Nat) → OddDist a a_1 → Prop}
  {a✝ a✝¹ : Nat} (t : OddDist a✝ a✝¹) (F_1 : ∀ (a a_1 : Nat) (t : EvenDist a a_1), t.below → motive_1 a a_1 t)
  (F_2 : ∀ (a a_1 : Nat) (t : OddDist a a_1), t.below → motive_2 a a_1 t) : motive_2 a✝ a✝¹ t
-/
#guard_msgs in
#check OddDist.brecOn

mutual

theorem OddDist.recTest {a b} (h : OddDist b a) : True :=
  match h with
  | .succ_left h => h.recTest
  | .succ_right h => h.recTest
termination_by structural h

theorem OddDist.recTest' {a b} (h : OddDist b a) : True :=
  match h with
  | .succ_left h => h.recTest
  | .succ_right h => h.recTest
termination_by structural h

theorem EvenDist.recTest (h : EvenDist a b) : True :=
  match h with
  | .zero => trivial
  | .succ_left h => (h 3).recTest
  | .succ_right h => h.recTest'
termination_by structural h

end

/-!
Nested inductives
-/

inductive Test (p : Nat → Prop) : Nat → Prop
  | zero : Test p 0
  | one (h : Test p 3 ∧ p 2) : Test p 1

/--
info: Test.brecOn {p : Nat → Prop} {motive_1 : (a : Nat) → Test p a → Prop} {motive_2 : Test p 3 ∧ p 2 → Prop} {a✝ : Nat}
  (t : Test p a✝) (F_1 : ∀ (a : Nat) (t : Test p a), t.below → motive_1 a t)
  (F_2 : ∀ (t : Test p 3 ∧ p 2), Test.below_1 t → motive_2 t) : motive_1 a✝ t
-/
#guard_msgs in
#check Test.brecOn

/--
info: Test.brecOn_1 {p : Nat → Prop} {motive_1 : (a : Nat) → Test p a → Prop} {motive_2 : Test p 3 ∧ p 2 → Prop}
  (t : Test p 3 ∧ p 2) (F_1 : ∀ (a : Nat) (t : Test p a), t.below → motive_1 a t)
  (F_2 : ∀ (t : Test p 3 ∧ p 2), Test.below_1 t → motive_2 t) : motive_2 t
-/
#guard_msgs in
#check Test.brecOn_1

-- nested recursion
theorem Test.recTest (h : Test p n) : True :=
  match h with
  | .zero => trivial
  | .one ⟨h, h'⟩ => recTest h
termination_by structural h

-- mutual nested recursion
mutual

theorem Test.recTest2 (h : Test p n) : True :=
  match h with
  | .zero => trivial
  | .one h => recTest3 h
termination_by structural h

theorem Test.recTest3 (h : Test p 3 ∧ p 2) : True :=
  match h with
  | ⟨h, _⟩ => recTest2 h
termination_by structural h

end

/-!
Reflexive inductives
-/

inductive Test2 (p : Nat → Prop) : Nat → Prop
  | zero : Test2 p 0
  | abc (h : ∀ n, p (a + n) → Test2 p n) : Test2 p a

/--
info: Test2.brecOn {p : Nat → Prop} {motive : (a : Nat) → Test2 p a → Prop} {a✝ : Nat} (t : Test2 p a✝)
  (F_1 : ∀ (a : Nat) (t : Test2 p a), Test2.below t → motive a t) : motive a✝ t
-/
#guard_msgs in
#check Test2.brecOn

theorem Test2.recTest (h : Test2 (fun _ => True) n) : True :=
  match h with
  | .zero => trivial
  | .abc h => recTest (h 0 trivial)
termination_by structural h

/-!
Nested inductives with indices
-/

set_option inductive.autoPromoteIndices false in
inductive And2 (p : Prop) : (q : Prop) → Prop where
  | intro (left : p) (right : b) : And2 p b

inductive Test' (p : Nat → Prop) : Nat → Prop where
  | zero : Test' p 0
  | one (h : And2 (Test' p 2) (p 3)) : Test' p 1

/--
info: Test'.brecOn {p : Nat → Prop} {motive_1 : (a : Nat) → Test' p a → Prop}
  {motive_2 : (q : Prop) → And2 (Test' p 2) q → Prop} {a✝ : Nat} (t : Test' p a✝)
  (F_1 : ∀ (a : Nat) (t : Test' p a), t.below → motive_1 a t)
  (F_2 : ∀ (q : Prop) (t : And2 (Test' p 2) q), Test'.below_1 t → motive_2 q t) : motive_1 a✝ t
-/
#guard_msgs in
#check Test'.brecOn

theorem Test'.recTest (h : Test p n) : True :=
  match h with
  | .zero => trivial
  | .one ⟨h, h'⟩ => recTest h
termination_by structural h

/-!
Recursion with the same inductive twice
-/

inductive NatProp : Prop where
  | zero
  | succ (k : NatProp) : NatProp

mutual

theorem NatProp.recTest1 (_a : Nat) (x : NatProp) (_c : Nat) : True :=
  match x with
  | .zero => trivial
  | .succ k =>
    have := k.recTest2 7
    this 3
termination_by structural x

theorem NatProp.recTest2 (_b : Nat) (x : NatProp) (_d : Nat) : True :=
  match x with
  | .zero => trivial
  | .succ k => k.recTest1 3 5
termination_by structural x

end

/-!
Support for named patterns
-/

mutual

inductive TestEven (b : Bool) : Nat → Prop where
  | zero : TestEven b 0
  | succ (h : Nat → TestOdd b n) (a : Nat) : TestEven b (n + 1)

inductive TestOdd (b : Bool) : Nat → Prop where
  | succ (h : TestEven b n) : TestOdd b (n + 1)

end

theorem TestEven.recTest {b : Bool} {n : Nat} (h : TestEven b n) (_a : Bool) : True :=
  match h with
  | .zero => trivial
  | @TestEven.succ _ n h' _a =>
    match h' 2 with
    | .succ .zero => trivial
    | .succ h₁@hh₁:(.succ h'' _) =>
      have : True := match h'' 3 with
        | .succ h''' => h'''.recTest false
      have := h₁
      have := hh₁
      have := h₁.recTest
      trivial
termination_by structural h

/-!
Matching on partial applications
-/

theorem TestEven.recTest2 {b : Bool} {n : Nat} (h : TestEven b n) : True :=
  match h with
  | .zero => trivial
  | @TestEven.succ _ n h' _a =>
    -- h' : ∀ (a : Nat), TestOdd b n
    match n, h' with
    | _ + 1, h'' =>
      match h'' 2 with
      | .succ h''' => h'''.recTest2
    | 0, _ => trivial
termination_by structural h

/-!
Recursive calls as part of match discriminants
-/

def addProofDependency {p : Prop} (_h : p) (a : α) : α := a

theorem NatProp.recTest3 (p : NatProp) : True :=
  match p with
  | .zero => trivial
  | .succ h =>
    match addProofDependency h.recTest3 trivial, h with
    | ⟨⟩, .zero => trivial
    | ⟨⟩, .succ h => h.recTest3
termination_by structural p

/-!
Using the same match twice
-/

theorem NatProp.recTest4 (p : NatProp) : True :=
  match p with
  | .zero => trivial
  | .succ h =>
    match h with
    | .zero => trivial
    | .succ h' =>
      have := h.recTest3
      h'.recTest4
termination_by structural p

/-!
Recursion on universe polymorphic functions
-/

class SuccTest (α : Type u) where
  succ : α → α

inductive SuccTest.le {α : Type u} [SuccTest α] : α → α → Prop where
  | refl {n : α} : le n n
  | step {a b : α} (h : le a b) : le a (SuccTest.succ b)

theorem SuccTest.le_trans {α : Type u} [SuccTest α] {a b c : α} : le a b → le b c → le a c
  | h, .refl => h
  | h, .step h' => .step (le_trans h h')
termination_by structural _ h => h
