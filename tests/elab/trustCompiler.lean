import Std.Tactic.BVDecide

/-!
Declarations using native computation (`native_decide`, `decide +native`, `bv_decide`) are rejected
unless `trustCompiler` is set.
-/

/--
error: declaration uses native computation, which requires trusting the Lean compiler

The axiom `byNativeDecide._native.native_decide.ax_1_1` asserts the result of compiling and running code instead of a proof checked by the kernel. Relying on it means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem byNativeDecide : 2 + 2 = 4 := by native_decide

/--
error: declaration uses native computation, which requires trusting the Lean compiler

The axiom `_example._native.decide.ax_1` asserts the result of compiling and running code instead of a proof checked by the kernel. Relying on it means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
example : 2 + 2 = 4 := by decide +native

/--
error: declaration uses native computation, which requires trusting the Lean compiler

The axiom `byBVDecide._native.bv_decide.ax_1_5` asserts the result of compiling and running code instead of a proof checked by the kernel. Relying on it means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem byBVDecide (x y : BitVec 8) : (x &&& y) + (x ^^^ y) = x ||| y := by bv_decide

/-! The axiom is created by the tactic, but the error is reported for the declaration. -/

/--
error: declaration uses native computation, which requires trusting the Lean compiler

The axiom `twoTactics._native.native_decide.ax_1_1` asserts the result of compiling and running code instead of a proof checked by the kernel. Relying on it means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem twoTactics : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor
  · native_decide
  · native_decide

/-! Nested proofs are not abstracted into auxiliary lemmas, so the error is reported once. -/

/--
error: declaration uses native computation, which requires trusting the Lean compiler

The axiom `nested._native.native_decide.ax_1` asserts the result of compiling and running code instead of a proof checked by the kernel. Relying on it means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
def nested : { n : Nat // n = 3 } × { n : Nat // n = 4 } :=
  (⟨3, by native_decide⟩, ⟨4, by native_decide⟩)

/-! Like the `sorry` warning, the check only looks at the declaration itself. -/

set_option trustCompiler true in
theorem trusted : 2 + 2 = 4 := by native_decide

#guard_msgs in
theorem usesTrusted : 2 + 2 = 4 := trusted

/-! Nested proofs are still abstracted when native computation is allowed. -/

set_option trustCompiler true in
def nestedAllowed : { n : Nat // n = 3 } × { n : Nat // n = 4 } :=
  (⟨3, by native_decide⟩, ⟨4, by native_decide⟩)

/--
info: theorem nestedAllowed._proof_1 : 3 = 3 :=
of_decide_eq_true nestedAllowed._native.native_decide.ax_1
-/
#guard_msgs in
#print nestedAllowed._proof_1

/-! The option can be set for the rest of the file. -/

set_option trustCompiler true

#guard_msgs in
theorem allowed : 2 + 2 = 4 := by native_decide

#guard_msgs in
theorem allowedBV (x y : BitVec 8) : (x &&& y) + (x ^^^ y) = x ||| y := by bv_decide
