/-!
  # Allow induction and cases to find instance target arguments which are not found by unification

  When unification with explicit targets fails to supply all implicit target arguments,
  as a last effort to provide instance-implicit arguments, the elaborator will try synthesis.
-/
class Foo (α : Type) where
  x : Nat

instance : Foo Nat where
  x := 0

/-!
  In this example, we have an induction principle Foo.induction where `(α : Type)` and `[ohno : Foo α]` are targets.
  The `ohno` target cannot be solved by unification of a later argument.
  However, we *are* able to solve for the argument by instance synthesis, so we should try to do so.
  When making this attempt fails, an error should be thrown which makes clear that we need this instance.
-/
section

@[elab_as_elim]
def Foo.induction (P : ∀ (α : Type) [Foo α], Prop) (nat : P Nat) (α : Type) [ohno : Foo α] : P α := sorry

/-! elaboration is able to infer [Foo α] -/
example (α : Type) [Foo α] : α = Nat := by
  induction α using Foo.induction with
  | nat => rfl


/-! elaboration synthesizes the right instance -/
set_option pp.explicit true in
example (α : Type) {noninst : Foo α} [inst:Foo α] : noninst.x = inst.x := by?
  induction α using Foo.induction with
  | nat => rfl

/-! elaboration shows a "failed to synthesize" error when the instance can't be synthesized -/
example (α : Type) : α = Nat := by
  induction α using Foo.induction with
  | nat => rfl
end

structure Bar (α : Type) [Foo α] : Type where
  hy : Foo.x α = 2

@[elab_as_elim]
def Bar.induction (P : ∀ (α : Type) [Foo α] (b: Bar α), Prop)
  (α : Type) [ohno : Foo α] (x : Bar α) (nat : ∀ (x : Bar Nat), P Nat x) : P α x := sorry


set_option pp.all true in
/-! unification provides `noninst` as correct target instead of finding `inst` via synthesis -/
example (α : Type) {noninst : Foo α} [inst : Foo α] (x:@Bar α noninst) : Nonempty (@Bar α noninst) := by
  induction α, x using Bar.induction with
  | nat x => exact Nonempty.intro x
