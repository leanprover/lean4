import Std.Tactic.BVDecide
import Lean

/-!
Declarations using native computation (`native_decide`, `decide +native`) are rejected unless
`trustEvalAsAxioms` is set. The error is reported at the tactic invocation. `bv_decide` is exempt.
-/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `byNativeDecide._native.native_decide.ax_1_1` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem byNativeDecide : 2 + 2 = 4 := by native_decide

/--
error: `decide +native` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `_example._native.decide.ax_1` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
example : 2 + 2 = 4 := by decide +native

/-! `bv_decide` is exempt, also when its proof ends up in an auxiliary lemma. -/

#guard_msgs in
theorem byBVDecide (x y : BitVec 8) : (x &&& y) + (x ^^^ y) = x ||| y := by
  bv_decide (config := { acNf := true })

#guard_msgs in
def nestedBV : { x : BitVec 8 // ∀ y, (x &&& y) + (x ^^^ y) = x ||| y } :=
  ⟨3, by intro y; bv_decide⟩

/-! Other tactics using `nativeEqTrue` are rejected by default, at the current ref. -/

open Lean Elab Tactic Meta in
elab "my_native" : tactic => liftMetaFinishingTactic fun g => do
  let b ← mkDecide (← g.getType)
  let .success prf ← nativeEqTrue `my_native b | throwError "not true"
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) (← g.getType) b.appArg! prf)

/--
error: `my_native` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `byMyNative._native.my_native.ax_1_1` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem byMyNative : 2 + 2 = 4 := by my_native

/-! Each invocation is reported. -/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `twoTactics._native.native_decide.ax_1_1` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
---
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `twoTactics._native.native_decide.ax_1_2` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem twoTactics : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor
  · first | fail | native_decide
  · native_decide

/-! Also when the proofs end up in auxiliary lemmas. -/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `nested._native.native_decide.ax_1` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
---
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `nested._native.native_decide.ax_2` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
def nested : { n : Nat // n = 3 } × { n : Nat // n = 4 } :=
  (⟨3, by native_decide⟩, ⟨4, by native_decide⟩)

/-! A macro expanding to a native computation tactic is reported at its invocation. -/

macro "my_native_decide" : tactic => `(tactic| native_decide)

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `byMacro._native.native_decide.ax_1_1` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
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

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `unusedHave._native.native_decide.ax_1_1` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem unusedHave : 2 + 2 = 4 := by
  have : 3 + 3 = 6 := by native_decide
  rfl

/-! An invocation that runs several times, e.g. via `<;>`, is reported once. -/

/--
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axioms `allGoals._native.native_decide.ax_1_1`, `allGoals._native.native_decide.ax_1_2` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
theorem allGoals : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor <;> native_decide

/-! Like the `sorry` warning, the check only looks at the declaration itself. -/

set_option trustEvalAsAxioms true in
theorem trusted : 2 + 2 = 4 := by native_decide

#guard_msgs in
theorem usesTrusted : 2 + 2 = 4 := trusted

/-! Referring to the axiom of another declaration explicitly is like referring to that declaration. -/

set_option Elab.async false in
set_option trustEvalAsAxioms true in
theorem trustedSync : 2 + 2 = 4 := by native_decide

#guard_msgs in
theorem usesTrustedAxiom : 2 + 2 = 4 := of_decide_eq_true trustedSync._native.native_decide.ax_1

/-! Nested proofs are abstracted into auxiliary lemmas as usual. -/

set_option trustEvalAsAxioms true in
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

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `nestedAgain._native.native_decide.ax_1` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
---
error: `native_decide` uses native computation, which requires trusting the Lean compiler

It proves the goal by evaluating code like `#eval` does, following `@[implemented_by]` and `@[extern]` implementations, and asserting the result as a new axiom, instead of constructing a proof that the kernel can check. Relying on such a proof means trusting the Lean compiler and all `@[implemented_by]` and `@[extern]` implementations involved, in addition to the kernel. `#print axioms` lists the axiom `nestedAgain._native.native_decide.ax_2` for this declaration and every declaration depending on it, and `lake comparator` and `lake check` fail on them.

If this is acceptable, native computation can be allowed for a single declaration using `set_option trustEvalAsAxioms true in`, or for an entire project by setting `trustEvalAsAxioms` to `true` in the `leanOptions` of the Lake package configuration.
-/
#guard_msgs in
def nestedAgain : { n : Nat // n = 3 } × { n : Nat // n = 4 } :=
  (⟨3, by native_decide⟩, ⟨4, by native_decide⟩)

/-! The option can be set for the rest of the file. -/

set_option trustEvalAsAxioms true

#guard_msgs in
theorem allowed : 2 + 2 = 4 := by native_decide

#guard_msgs in
theorem allowedBV (x y : BitVec 8) : (x &&& y) + (x ^^^ y) = x ||| y := by bv_decide
