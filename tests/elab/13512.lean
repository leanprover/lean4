module

/-!
  Test that matching on the output of an implicit reducible function does not reduces the function at default transparency.
  Previous version of Lean (e.g. v4.30) would perform such a reduction.
-/

section ImplicitReducibleFunction

@[implicit_reducible]
def f (n: Nat): Nat × Nat :=
  (n, 2*n)

/--
trace: n : Nat
⊢ (f n).snd = (f n).fst + (f n).fst
---
warning: declaration uses `sorry`
-/
#guard_msgs in
-- Test with dsimp only.
-- Lean v4.30 would leave the goal `2 * n = n + n`
-- (hence unfolding the definition of `f`)
theorem test_dsimp_f (n: Nat):
  let (n1, n2) := f n
  n2 = n1 + n1
:= by
  dsimp only
  trace_state
  sorry

-- Test with grind preprocessing.
-- Lean v4.30 would fail, because `grind` preprocessing
-- would leave the goal `n = (f n).fst ∧ 2*n = (f n).snd`
-- which cannot be proved without inspecting the definition of `f`
theorem test_grind_f (n: Nat):
  let (n1, n2) := f n
  n1 = (f n).fst ∧ n2 = (f n).snd
:= by
  grind

section ImplicitReducibleFunction

-- same tests, but using a typeclass instance instead of @[implicit_reducible] annotation.
section TypeclassInstanceFunction

class C (α: Type) where
  g: α → α × α

instance: C Nat where
  g n := (n, 2*n)

/--
trace: n : Nat
⊢ (C.g n).snd = (C.g n).fst + (C.g n).fst
---
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem test_dsimp_g (n: Nat):
  let (n1, n2) := C.g n
  n2 = n1 + n1
:= by
  dsimp only
  trace_state
  sorry

theorem test_grind_g (n: Nat):
  let (n1, n2) := C.g n
  n1 = (C.g n).fst ∧ n2 = (C.g n).snd
:= by
  grind

end TypeclassInstanceFunction
