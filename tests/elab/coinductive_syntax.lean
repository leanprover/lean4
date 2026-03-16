-- set_option trace.Elab.coinductive true
set_option pp.proofs true
section
variable (α : Type)

/--
docstring
-/
coinductive infSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq r b → infSeq r a

/--
info: infSeq.step (α : Type) (r : α → α → Prop) {a b : α} : r a b → infSeq α r b → infSeq α r a
-/
#guard_msgs in
#check infSeq.step

theorem casesOnTest (r : α → α → Prop) (a : α) : infSeq α r a → ∃ b, r a b := by
  intro h
  cases h
  case step b _ hr => exists b

-- `match` support does not work yet
/--
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`

Hint: Using one of these would be valid:
  [apply] `Nat.le.step`
  [apply] `Nat.le.below.step`
  [apply] `Lean.Order.iterates.below.step`
  [apply] `Lean.Order.iterates.step`
  [apply] `infSeq._functor.step`
---
error: Case tag `rhs` not found.

Note: There are no cases to select.
-/
#guard_msgs in
theorem casesOnTest' (r : α → α → Prop) (a : α) : infSeq α r a → ∃ b, r a b := by
  intro h
  match h with
  | step  b _ hr => exists b

/--
info: infSeq.casesOn (α : Type) (r : α → α → Prop) {motive : (a : α) → infSeq α r a → Prop} {a✝ : α} (t : infSeq α r a✝)
  (step : ∀ {a b : α} (a_1 : r a b) (a_2 : infSeq α r b), motive a (infSeq.step α r a_1 a_2)) : motive a✝ t
-/
#guard_msgs in
#check infSeq.casesOn

/--
info: infSeq.functor_unfold (α : Type) (r : α → α → Prop) (a✝ : α) : infSeq α r a✝ = infSeq._functor α r (infSeq α r) a✝
-/
#guard_msgs in
#check infSeq.functor_unfold

/-- info: infSeq (α : Type) (r : α → α → Prop) : α → Prop -/
#guard_msgs in
#check infSeq

/--
info: inductive infSeq._functor : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop
number of parameters: 3
constructors:
infSeq._functor.step : ∀ (α : Type) (r : α → α → Prop) (infSeq._functor.call : α → Prop) {a b : α},
  r a b → infSeq._functor.call b → infSeq._functor α r infSeq._functor.call a
-/
#guard_msgs in
#print infSeq._functor

/--
info: def infSeq._functor.existential : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop :=
fun α r infSeq._functor.call a => ∃ b, r a b ∧ infSeq._functor.call b
-/
#guard_msgs in
#print infSeq._functor.existential

/--
info: infSeq._functor.existential_equiv (α : Type) (r : α → α → Prop) (infSeq._functor.call : α → Prop) (a✝ : α) :
  infSeq._functor α r infSeq._functor.call a✝ ↔ ∃ b, r a✝ b ∧ infSeq._functor.call b
-/
#guard_msgs in
#check infSeq._functor.existential_equiv

/--
info: infSeq.coinduct (α : Type) (r : α → α → Prop) (pred : α → Prop) (hyp : ∀ (a : α), pred a → ∃ b, r a b ∧ pred b)
  (a✝ : α) : pred a✝ → infSeq α r a✝
-/
#guard_msgs in
#check infSeq.coinduct

/--
info: infSeq.step (α : Type) (r : α → α → Prop) {a b : α} : r a b → infSeq α r b → infSeq α r a
-/
#guard_msgs in
#check infSeq.step
end

section
mutual
  coinductive tick : Prop where
  | mk : ¬tock → tick

  inductive tock : Prop where
  | mk : ¬tick → tock
end

/--
info: tick._functor.casesOn {tick._functor.call tock._functor.call : Prop}
  {motive_1 : tick._functor tick._functor.call tock._functor.call → Prop}
  (t : tick._functor tick._functor.call tock._functor.call)
  (mk : ∀ (a : ¬tock._functor.call), motive_1 (tick._functor.mk tick._functor.call tock._functor.call a)) : motive_1 t
-/
#guard_msgs in
#check tick._functor.casesOn

/-- info: tick.mk : ¬tock → tick -/
#guard_msgs in
#check tick.mk

/-- info: tock.mk : ¬tick → tock -/
#guard_msgs in
#check tock.mk

/-- info: tock._functor (tick._functor.call tock._functor.call : Prop) : Prop -/
#guard_msgs in
#check tock._functor

/-- info: tock._functor.existential (tick._functor.call tock._functor.call : Prop) : Prop -/
#guard_msgs in
#check tock._functor.existential

/--
info: tick.coinduct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 → False) (hyp_2 : (pred_1 → False) → pred_2) :
  pred_1 → tick
-/
#guard_msgs in
#check tick.coinduct

/--
info: tock._functor.existential_equiv (tick._functor.call tock._functor.call : Prop) :
  tock._functor tick._functor.call tock._functor.call ↔ ¬tick._functor.call
-/
#guard_msgs in
#check tock._functor.existential_equiv

/--
info: tock.induct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 → False) (hyp_2 : (pred_1 → False) → pred_2) : tock → pred_2
-/
#guard_msgs in
#check tock.induct

/--
info: tick.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 → False) (hyp_2 : (pred_1 → False) → pred_2) :
  (pred_1 → tick) ∧ (tock → pred_2)
-/
#guard_msgs in
#check tick.mutual_induct
end

/-- error: `coinductive` keyword can only be used to define predicates -/
#guard_msgs in
coinductive my_nat  where
  | zero : my_nat
  | succ : my_nat → my_nat

def Set := Nat → Prop

coinductive Foo : Set where

/--
info: Foo.coinduct (pred : Set) (hyp : ∀ (a : Nat), pred a → False) (a✝ : Nat) : pred a✝ → Foo a✝
-/
#guard_msgs in
#check Foo.coinduct

coinductive Bar : Set where
  | make : Bar 42

/--
info: Bar.coinduct (pred : Set) (hyp : ∀ (a : Nat), pred a → a = 42) (a✝ : Nat) : pred a✝ → Bar a✝
-/
#guard_msgs in
#check Bar.coinduct


coinductive dependentTest : (n : Nat) → (Vector α n) → Prop  where
  | mk (x : α) : dependentTest m v → dependentTest (m+1) (v.push x)

/--
info: dependentTest.coinduct.{u_1} {α : Type u_1} (pred : (n : Nat) → Vector α n → Prop)
  (hyp : ∀ (n : Nat) (a : Vector α n), pred n a → ∃ m v x, pred m v ∧ n = m + 1 ∧ a ≍ v.push x) (n : Nat)
  (a✝ : Vector α n) : pred n a✝ → dependentTest n a✝
-/
#guard_msgs in
#check dependentTest.coinduct

/-
  Duplicated parameters and dependent types
-/
coinductive dependentTest2 : (n : Nat) → (m : Nat) → (Vector α (m + n)) → (Vector α (m + n)) → Prop  where
  | mk (x : α) : dependentTest2 0 n v v → dependentTest2 0 (n + 1) (v.push x) (v.push x)

coinductive dependentTest3 : (α : Type) → (ls : List α) → (vec : Vector α ls.length) → (Vector α vec.size) → Prop where
  | mk : dependentTest3 Nat [a] (Vector.singleton a) (Vector.singleton a)
  | mk2 : dependentTest3 String ["hi"] (Vector.singleton b) (Vector.singleton c)

/--
info: dependentTest3.casesOn
  {motive :
    (α : Type) →
      (ls : List α) → (vec : Vector α ls.length) → (a : Vector α vec.size) → dependentTest3 α ls vec a → Prop}
  {α : Type} {ls : List α} {vec : Vector α ls.length} {a✝ : Vector α vec.size} (t : dependentTest3 α ls vec a✝)
  (mk : ∀ {a : Nat}, motive Nat [a] (Vector.singleton a) (Vector.singleton a) dependentTest3.mk)
  (mk2 : ∀ {b c : String}, motive String ["hi"] (Vector.singleton b) (Vector.singleton c) dependentTest3.mk2) :
  motive α ls vec a✝ t
-/
#guard_msgs in
#check dependentTest3.casesOn

coinductive test1  (r: α → α → Prop) : α → α → Prop where
  | mk : r a b → test1 r a b → test1 r a a
  | mk2 : test1 r a a

coinductive test2  (r: α → α → Prop) : α → α → Prop where
  | mk : r a b → test2 r b b → test2 r a a

/--
error: Cannot define an coinductive predicate and a constructor with the same name `A.mk`
---
error: Cannot define an coinductive predicate and a constructor with the same name `A.mk`
-/
#guard_msgs in
mutual
  coinductive A : Prop where
    | mk : A.mk → A
  coinductive A.mk : Prop where
    | mk : A → A.mk
end

macro "test%" : command => `(command|
  coinductive MacroTest : Prop where | mk : MacroTest
)

/-- error: Coinductive predicates are not allowed inside of macro scopes -/
#guard_msgs in
test%

namespace unsafe_test
unsafe coinductive infSeq2 (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq2 r b → infSeq2 r a
end unsafe_test

/--
@ +4:14...20
error: `coinductive` keyword can only be used to define predicates
-/
#guard_msgs (positions := true) in
mutual
  coinductive wrong1 : Prop where

  coinductive wrong2  where
    | zero : wrong2
    | succ : wrong1 → wrong2
end
