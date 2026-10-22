/-!
Tests for `backward.isDefEq.respectTransparency.instanceTypes`: assignments to class-typed
metavariables (of type `C as` or `∀ xs, C as`) must preserve the metavariable's type up to
`.instances` transparency, whatever their binder kind and wherever they come from.
-/

class MyAdd (α : Type) where
  add : α → α → α

instance : MyAdd Nat := ⟨Nat.add⟩

/-- Unfolds at `.implicit` transparency, but not at `.instances` transparency. -/
@[implicit_reducible] def Copy (α : Type) := α

def double {α : Type} [MyAdd α] (a : α) : α := MyAdd.add a a

theorem double_def {α : Type} [MyAdd α] (a : α) : double a = MyAdd.add a a := rfl

theorem double_def' {α : Type} {inst : MyAdd α} (a : α) : @double α inst a = MyAdd.add a a := rfl

/-!
`inst : MyAdd (Copy Nat)` is used as an instance of `MyAdd Nat`. Rewriting with `double_def` would
assign the instance metavariable of `double_def`, of type `MyAdd Nat`, the value `inst`.
-/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  double ?a
in the target expression
  double a = MyAdd.add a a

inst : MyAdd (Copy Nat)
a : Nat
⊢ double a = MyAdd.add a a
-/
#guard_msgs in
example (inst : MyAdd (Copy Nat)) (a : Nat) : @double Nat inst a = @MyAdd.add Nat inst a a := by
  rw [double_def]

/-!
With the check disabled, unification succeeds, and `rw` reports the mismatch only when it compares
the assigned instance against the synthesized one.
-/

/--
error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instMyAddNat
inferred
  inst
-/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceTypes false in
example (inst : MyAdd (Copy Nat)) (a : Nat) : @double Nat inst a = @MyAdd.add Nat inst a a := by
  rw [double_def]

/-! The check also applies to class-typed metavariables created for implicit arguments. -/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  double ?a
in the target expression
  double a = MyAdd.add a a

inst : MyAdd (Copy Nat)
a : Nat
⊢ double a = MyAdd.add a a
-/
#guard_msgs in
example (inst : MyAdd (Copy Nat)) (a : Nat) : @double Nat inst a = @MyAdd.add Nat inst a a := by
  rw [double_def']

#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceTypes false in
example (inst : MyAdd (Copy Nat)) (a : Nat) : @double Nat inst a = @MyAdd.add Nat inst a a := by
  rw [double_def']

/-! The old option `instanceSearchTypes` disables the check as well. -/

#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
example (inst : MyAdd (Copy Nat)) (a : Nat) : @double Nat inst a = @MyAdd.add Nat inst a a := by
  rw [double_def']

/-! Instances of the expected type are accepted. -/

#guard_msgs in
example (inst : MyAdd Nat) (a : Nat) : @double Nat inst a = @MyAdd.add Nat inst a a := by
  rw [double_def]

/-! Metavariables whose type is a function type returning a class are checked as well. -/

def countP (p : Nat → Prop) [inst : ∀ n, Decidable (p n)] (l : List Nat) : Nat :=
  (l.filter fun n => decide (p n)).length

theorem countP_def (p : Nat → Prop) [∀ n, Decidable (p n)] (l : List Nat) :
    countP p l = (l.filter fun n => decide (p n)).length := rfl

def IsZero (n : Nat) : Prop := n = 0

instance : DecidablePred IsZero := fun n => inferInstanceAs (Decidable (n = 0))

/-- Unfolds at `.implicit` transparency, but not at `.instances` transparency. -/
@[implicit_reducible] def IsZero' := IsZero

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  countP ?p ?l
in the target expression
  countP IsZero [] = 0

inst : (n : Nat) → Decidable (IsZero' n)
⊢ countP IsZero [] = 0
-/
#guard_msgs in
example (inst : ∀ n, Decidable (IsZero' n)) : @countP IsZero inst [] = 0 := by
  rw [countP_def]

#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceTypes false in
example (inst : ∀ n, Decidable (IsZero' n)) : @countP IsZero inst [] = 0 := by
  rw [countP_def]
  rfl
