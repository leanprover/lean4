/-!
Tests for `backward.instanceTypes.subsingletons` and its children `.decidable` and `.prop`: they
exempt `Decidable` instances and instances of `Prop`-valued classes from the instance-type checks
of the unifier (`backward.isDefEq.respectTransparency.instanceTypes`) and of `simp`/`dsimp`
(`backward.dsimp.instanceTypes`).
-/

def IsZero (n : Nat) : Prop := n = 0

instance : DecidablePred IsZero := fun n => inferInstanceAs (Decidable (n = 0))

/-- Unfolds at `.implicit` transparency, but not at `.instances` transparency. -/
@[implicit_reducible] def IsZero' := IsZero

class IsNice (n : Nat) : Prop where

instance : IsNice 0 := ⟨⟩

/-- Unfolds at `.implicit` transparency, but not at `.instances` transparency. -/
@[implicit_reducible] def zero' : Nat := 0

def nice (n : Nat) [IsNice n] : Nat := n

class NiceT (α : Type) : Prop where

instance : NiceT Nat := ⟨⟩

/-- Unfolds at `.implicit` transparency, but not at `.instances` transparency. -/
@[implicit_reducible] def Nat' : Type := Nat

def Box (α : Type) [NiceT α] : Type := α

theorem ite_eq_left' {α : Type} {c : Prop} {h : Decidable c} (hc : c) (t e : α) :
    @ite α c h t e = t := by
  cases h with
  | isTrue _ => rfl
  | isFalse h' => exact absurd hc h'

theorem nice_def {n : Nat} {h : IsNice n} : @nice n h = n := rfl

def P {α : Type} (_ : α) : Prop := True

/-! The unifier: `inst` has the expected type only at `.implicit` transparency. -/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  if IsZero 0 then 1 else 2
in the target expression
  (if IsZero 0 then 1 else 2) = 1

inst : Decidable (IsZero' 0)
⊢ (if IsZero 0 then 1 else 2) = 1
-/
#guard_msgs in
example (inst : Decidable (IsZero' 0)) : @ite Nat (IsZero 0) inst 1 2 = 1 := by
  rw [ite_eq_left' (c := IsZero 0) rfl 1 2]

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  nice 0
in the target expression
  nice 0 = 0

inst : IsNice zero'
⊢ nice 0 = 0
-/
#guard_msgs in
example (inst : IsNice zero') : @nice 0 inst = 0 := by
  rw [nice_def (n := 0)]

example (inst : Decidable (IsZero' 0)) : @ite Nat (IsZero 0) inst 1 2 = 1 := by
  set_option backward.instanceTypes.subsingletons.decidable false in
  rw [ite_eq_left' (c := IsZero 0) rfl 1 2]

example (inst : Decidable (IsZero' 0)) : @ite Nat (IsZero 0) inst 1 2 = 1 := by
  set_option backward.instanceTypes.subsingletons false in
  rw [ite_eq_left' (c := IsZero 0) rfl 1 2]

example (inst : IsNice zero') : @nice 0 inst = 0 := by
  set_option backward.instanceTypes.subsingletons.prop false in
  rw [nice_def (n := 0)]

example (inst : IsNice zero') : @nice 0 inst = 0 := by
  set_option backward.instanceTypes.subsingletons false in
  rw [nice_def (n := 0)]

/-! Each child only exempts its own instances. -/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  if IsZero 0 then 1 else 2
in the target expression
  (if IsZero 0 then 1 else 2) = 1

inst : Decidable (IsZero' 0)
⊢ (if IsZero 0 then 1 else 2) = 1
-/
#guard_msgs in
example (inst : Decidable (IsZero' 0)) : @ite Nat (IsZero 0) inst 1 2 = 1 := by
  set_option backward.instanceTypes.subsingletons.prop false in
  rw [ite_eq_left' (c := IsZero 0) rfl 1 2]

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  nice 0
in the target expression
  nice 0 = 0

inst : IsNice zero'
⊢ nice 0 = 0
-/
#guard_msgs in
example (inst : IsNice zero') : @nice 0 inst = 0 := by
  set_option backward.instanceTypes.subsingletons.decidable false in
  rw [nice_def (n := 0)]

/-! Metavariables of function types returning `Decidable` count as `Decidable`. -/

def countP (p : Nat → Prop) [inst : ∀ n, Decidable (p n)] (l : List Nat) : Nat :=
  (l.filter fun n => decide (p n)).length

theorem countP_def (p : Nat → Prop) [∀ n, Decidable (p n)] (l : List Nat) :
    countP p l = (l.filter fun n => decide (p n)).length := rfl

example (inst : ∀ n, Decidable (IsZero' n)) : @countP IsZero inst [] = 0 := by
  set_option backward.instanceTypes.subsingletons.decidable false in
  rw [countP_def]
  rfl

/-! `simp`/`dsimp`: unfolding `IsZero'`, `zero'` or `Nat'` would leave `inst` with a type that
differs from the expected one at `.instances` transparency. Where `simp` can, it casts a `Prop`
instance instead, so the `simp` example rewrites a type argument. -/

/-- error: `dsimp` made no progress -/
#guard_msgs in
example (inst : Decidable (IsZero' 0)) : P (@ite Nat (IsZero' 0) inst 1 2) := by
  dsimp only [IsZero']

/-- error: `simp` made no progress -/
#guard_msgs in
example (inst : Decidable (IsZero' 0)) : P (@ite Nat (IsZero' 0) inst 1 2) := by
  simp only [IsZero']

/-- error: `dsimp` made no progress -/
#guard_msgs in
example (inst : IsNice zero') : P (@nice zero' inst) := by
  dsimp only [zero']

/-- error: `simp` made no progress -/
#guard_msgs in
example (inst : NiceT Nat') (x : @Box Nat' inst) : P x := by
  simp only [Nat']

example (inst : Decidable (IsZero' 0)) : P (@ite Nat (IsZero' 0) inst 1 2) := by
  set_option backward.instanceTypes.subsingletons.decidable false in
  dsimp only [IsZero']
  guard_target =ₛ P (@ite Nat (IsZero 0) inst 1 2)
  trivial

example (inst : Decidable (IsZero' 0)) : P (@ite Nat (IsZero' 0) inst 1 2) := by
  set_option backward.instanceTypes.subsingletons false in
  simp only [IsZero']
  guard_target =ₛ P (@ite Nat (IsZero 0) inst 1 2)
  trivial

example (inst : IsNice zero') : P (@nice zero' inst) := by
  set_option backward.instanceTypes.subsingletons.prop false in
  dsimp only [zero']
  guard_target =ₛ P (@nice 0 inst)
  trivial

example (inst : NiceT Nat') (x : @Box Nat' inst) : P x := by
  set_option backward.instanceTypes.subsingletons false in
  simp only [Nat']
  guard_target =ₛ @P (@Box Nat inst) x
  trivial

/-- error: `dsimp` made no progress -/
#guard_msgs in
example (inst : Decidable (IsZero' 0)) : P (@ite Nat (IsZero' 0) inst 1 2) := by
  set_option backward.instanceTypes.subsingletons.prop false in
  dsimp only [IsZero']

/-- error: `dsimp` made no progress -/
#guard_msgs in
example (inst : IsNice zero') : P (@nice zero' inst) := by
  set_option backward.instanceTypes.subsingletons.decidable false in
  dsimp only [zero']
