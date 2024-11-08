import Lean
/-!
# `native_decide`
-/

/-!
Simplest example.
-/
theorem ex1 : True := by native_decide
/-- info: 'ex1' depends on axioms: [Lean.ofReduceBool] -/
#guard_msgs in #print axioms ex1


/-!
The decidable instance is only evaluated once.
It is evaluated at elaboration time, hence stdout can be collected by `collect_stdout`.
-/

elab "collect_stdout " t:tactic : tactic => do
  let (out, _) ← IO.FS.withIsolatedStreams <| Lean.Elab.Tactic.evalTactic t
  Lean.logInfo m!"output: {out}"

def P (n : Nat) := ∃ k, n = 2 * k

instance instP : DecidablePred P :=
  fun
  | 0 => isTrue ⟨0, rfl⟩
  | 1 => isFalse (by intro ⟨k, h⟩; omega)
  | n + 2 =>
    dbg_trace "step";
    match instP n with
    | isTrue h => isTrue (by have ⟨k, h⟩ := h; exact ⟨k + 1, by omega⟩)
    | isFalse h => isFalse (by intro ⟨k, h'⟩; apply h; exists k - 1; omega)

/-- info: output: step -/
#guard_msgs in example : P 2 := by collect_stdout native_decide


/-!
The `native_decide` tactic can fail at elaboration time, rather than waiting until kernel checking.
-/

-- Check the error message
/--
error: tactic 'native_decide' evaluated that the proposition
  False
is false
-/
#guard_msgs in
example : False := by native_decide

/--
error: second case
⊢ False
-/
#guard_msgs in
example : False := by first | native_decide | fail "second case"


/-!
Reverting free variables.
-/

/--
error: expected type must not contain free variables
  x + 1 ≤ 5
Use the '+revert' option to automatically cleanup and revert free variables.
-/
#guard_msgs in
example (x : Nat) (h : x < 5) : x + 1 ≤ 5 := by native_decide

example (x : Nat) (h : x < 5) : x + 1 ≤ 5 := by native_decide +revert


/-!
Make sure `native_decide` fails at elaboration time.
https://github.com/leanprover/lean4/issues/2072
-/

/--
error: tactic 'native_decide' evaluated that the proposition
  False
is false
---
info: let_fun this := sorry;
this : False
-/
#guard_msgs in #check show False by native_decide


/--
Can handle universe levels.
-/

instance (p : PUnit.{u} → Prop) [Decidable (p PUnit.unit)] : Decidable (∀ x : PUnit.{u}, p x) :=
  decidable_of_iff (p PUnit.unit) (by constructor; rintro _ ⟨⟩; assumption; intro h; apply h)

example : ∀ (x : PUnit.{u}), x = PUnit.unit := by native_decide


/-!
Can't evaluate
-/

inductive ItsTrue : Prop
  | mk

instance : Decidable ItsTrue := sorry

/--
error: tactic 'native_decide' failed, could not evaluate decidable instance.
Error: cannot evaluate code because 'instDecidableItsTrue' uses 'sorry' and/or contains errors
-/
#guard_msgs in example : ItsTrue := by native_decide


/-!
Panic during evaluation
-/

inductive ItsTrue2 : Prop
  | mk

instance : Decidable ItsTrue2 :=
  have : Inhabited (Decidable ItsTrue2) := ⟨isTrue .mk⟩
  panic! "oh no"

-- Note: this test fails within VS Code
/-- info: output: PANIC at instDecidableItsTrue2 decideNative:126:2: oh no -/
#guard_msgs in example : ItsTrue2 := by collect_stdout native_decide
