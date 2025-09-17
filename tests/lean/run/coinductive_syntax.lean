section
variable (α : Type)
/--
docstring
-/
coinductive infSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq r b → infSeq r a


/-- info: infSeq (α : Type) (r : α → α → Prop) : α → Prop -/
#guard_msgs in
#check infSeq

/--
info: inductive infSeq_functor : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop
number of parameters: 3
constructors:
infSeq_functor.step : ∀ (α : Type) (r : α → α → Prop) (infSeq_functor.call : α → Prop) {a b : α},
  r a b → infSeq_functor.call b → infSeq_functor α r infSeq_functor.call a
-/
#guard_msgs in
#print infSeq_functor

/--
info: def infSeq_functor.existential : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop :=
fun α r infSeq_functor.call a => ∃ b, r a b ∧ infSeq_functor.call b
-/
#guard_msgs in
#print infSeq_functor.existential

/--
info: infSeq_functor.existential_equiv (α : Type) (r : α → α → Prop) (infSeq_functor.call : α → Prop) (a✝ : α) :
  infSeq_functor α r infSeq_functor.call a✝ ↔ ∃ b, r a✝ b ∧ infSeq_functor.call b
-/
#guard_msgs in
#check infSeq_functor.existential_equiv

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

/-- info: tick.mk : ¬tock → tick -/
#guard_msgs in
#check tick.mk

/-- info: tock.mk : ¬tick → tock -/
#guard_msgs in
#check tock.mk

/-- info: tock_functor (tick_functor.call tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check tock_functor

/-- info: tock_functor.existential (tick_functor.call tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check tock_functor.existential

/--
info: tick.coinduct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 → False) (hyp_2 : (pred_1 → False) → pred_2) :
  pred_1 → tick
-/
#guard_msgs in
#check tick.coinduct

/--
info: tock_functor.existential_equiv (tick_functor.call tock_functor.call : Prop) :
  tock_functor tick_functor.call tock_functor.call ↔ ¬tick_functor.call
-/
#guard_msgs in
#check tock_functor.existential_equiv

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

/-
  Duplicated parameters and dependent types
-/
coinductive dependentTest2 : (n : Nat) → (m : Nat) → (Vector α (m + n)) → (Vector α (m + n)) → Prop  where
  | mk (x : α) : dependentTest2 0 n v v → dependentTest2 0 (n + 1) (v.push x) (v.push x)
/-
  Even more complicated dependent test
-/
coinductive dependentTest3 : (α : Type) → (ls : List α) → (vec : Vector α ls.length) → (Vector α vec.size) → Prop where
  | mk : dependentTest3 Nat [a] (Vector.singleton a) (Vector.singleton a)

/--
info: dependentTest.coinduct.{u_1} {α : Type u_1} (pred : (n : Nat) → Vector α n → Prop)
  (hyp : ∀ (n : Nat) (a : Vector α n), pred n a → ∃ m v x, pred m v ∧ n = m + 1 ∧ a ≍ v.push x) (n : Nat)
  (a✝ : Vector α n) : pred n a✝ → dependentTest n a✝
-/
#guard_msgs in
#check dependentTest.coinduct

coinductive test1  (r: α → α → Prop) : α → α → Prop where
  | mk : r a b → test1 r a b → test1 r a a
  | mk2 : test1 r a a

coinductive test2  (r: α → α → Prop) : α → α → Prop where
  | mk : r a b → test2 r b b → test2 r a a

#check test1_functor.casesOn
