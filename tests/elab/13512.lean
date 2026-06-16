module

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
theorem test_dsimp_f (n: Nat):
  let (n1, n2) := f n
  n2 = n1 + n1
:= by
  dsimp only
  trace_state
  sorry

theorem test_grind_f (n: Nat):
  let (n1, n2) := f n
  n1 = (f n).fst ∧ n2 = (f n).snd
:= by
  grind

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
