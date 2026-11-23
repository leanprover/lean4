import Std.Tactic.BVDecide

/-!
Declarations using native computation (`native_decide`, `decide +native`, `bv_decide`) are rejected
unless `trustCompiler` is set. The error is reported at the tactic invocation.
-/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `byNativeDecide._native.native_decide.ax_1_1` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem byNativeDecide : 2 + 2 = 4 := by native_decide

/--
error: `decide +native` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `_example._native.decide.ax_1` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
example : 2 + 2 = 4 := by decide +native

/--
error: `bv_decide (config := { acNf := true })` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `byBVDecide._native.bv_decide.ax_1_5` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem byBVDecide (x y : BitVec 8) : (x &&& y) + (x ^^^ y) = x ||| y := by
  bv_decide (config := { acNf := true })

/-! Each invocation is reported. -/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `twoTactics._native.native_decide.ax_1_1` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
---
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `twoTactics._native.native_decide.ax_1_2` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem twoTactics : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor
  · first | fail | native_decide
  · native_decide

/-! Also when the proofs end up in auxiliary lemmas. -/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `nested._native.native_decide.ax_1` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
---
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `nested._native.native_decide.ax_2` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
def nested : { n : Nat // n = 3 } × { n : Nat // n = 4 } :=
  (⟨3, by native_decide⟩, ⟨4, by native_decide⟩)

/-! A macro expanding to a native computation tactic is reported at its invocation. -/

macro "my_native_decide" : tactic => `(tactic| native_decide)

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `byMacro._native.native_decide.ax_1_1` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem byMacro : 2 + 2 = 4 := by my_native_decide

/-! Native computation that was backtracked over is not part of the proof and not reported. -/

theorem backtrackedFirst : 2 + 2 = 4 := by
  first | (native_decide; fail) | rfl

theorem backtrackedTry : 2 + 2 = 4 := by
  try (native_decide; fail)
  rfl

/-! Native computation whose result is not needed is still part of the proof and reported. -/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `unusedHave._native.native_decide.ax_1_1` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem unusedHave : 2 + 2 = 4 := by
  have : 3 + 3 = 6 := by native_decide
  rfl

/-! An invocation that runs several times, e.g. via `<;>`, is reported once. -/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axioms `allGoals._native.native_decide.ax_1_1`, `allGoals._native.native_decide.ax_1_2` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem allGoals : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor <;> native_decide

/-! Like the `sorry` warning, the check only looks at the declaration itself. -/

set_option trustCompiler true in
theorem trusted : 2 + 2 = 4 := by native_decide

#guard_msgs in
theorem usesTrusted : 2 + 2 = 4 := trusted

/-! Referring to the axiom of another declaration explicitly is reported at the declaration. -/

set_option Elab.async false in
set_option trustCompiler true in
theorem trustedSync : 2 + 2 = 4 := by native_decide

/--
error: declaration uses native computation, which requires trusting the Lean compiler

The axiom `trustedSync._native.native_decide.ax_1` asserts the result of compiling and running code, instead of a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem usesTrustedAxiom : 2 + 2 = 4 := of_decide_eq_true trustedSync._native.native_decide.ax_1

/-! Nested proofs are abstracted into auxiliary lemmas as usual. -/

set_option trustCompiler true in
def nestedAllowed : { n : Nat // n = 3 } × { n : Nat // n = 4 } :=
  (⟨3, by native_decide⟩, ⟨4, by native_decide⟩)

/--
info: theorem nestedAllowed._proof_1 : 3 = 3 :=
of_decide_eq_true nestedAllowed._native.native_decide.ax_1
-/
#guard_msgs in
#print nestedAllowed._proof_1

/-! Auxiliary lemmas using native computation are not reused from the cache. -/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `nestedAgain._native.native_decide.ax_1` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
---
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by compiling and running code and asserting the result as an axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and interpreter, as well as all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. For the same reason, proofs using native computation are rejected by `lake comparator` and `lake check`. `#print axioms` lists the axiom `nestedAgain._native.native_decide.ax_2` for this declaration and every declaration depending on it.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustCompiler true in`, or for an entire project by setting `trustCompiler` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
def nestedAgain : { n : Nat // n = 3 } × { n : Nat // n = 4 } :=
  (⟨3, by native_decide⟩, ⟨4, by native_decide⟩)

/-! The option can be set for the rest of the file. -/

set_option trustCompiler true

#guard_msgs in
theorem allowed : 2 + 2 = 4 := by native_decide

#guard_msgs in
theorem allowedBV (x y : BitVec 8) : (x &&& y) + (x ^^^ y) = x ||| y := by bv_decide
