/-!
# `trace.Meta.Tactic.simp.backwardDefEq` reports `[backward_defeq]` rewrites

The trace class fires when `dsimp` (or the rfl-only mode of `simp`) uses a
`[backward_defeq]` lemma to rewrite — i.e. when the rewrite would not have
fired without `set_option backward.defeqAttrib.useBackward true`.
-/

def slow : Nat → Nat := fun n => n + 0

@[backward_defeq] theorem slow_eq (n : Nat) : slow n = n :=
  Nat.add_zero n

-- With `useBackward`, `slow_eq` fires and the trace is emitted.
set_option backward.defeqAttrib.useBackward true in
set_option trace.Meta.Tactic.simp.backwardDefEq true in
/--
trace: [Meta.Tactic.simp.backwardDefEq] used `[backward_defeq]` theorem slow_eq to rewrite
      slow 1
-/
#guard_msgs in
example : slow 1 = 1 := by dsimp only [slow_eq]

-- Without `useBackward`, `dsimp` cannot use `slow_eq` and there is no trace event.
set_option trace.Meta.Tactic.simp.backwardDefEq true in
/-- error: `dsimp` made no progress -/
#guard_msgs in
example : slow 1 = 1 := by dsimp only [slow_eq]

@[implicit_reducible] def fastApp (f : Nat → Nat) (n : Nat) : Nat := f n

@[defeq] theorem fastApp_eq (f : Nat → Nat) (n : Nat) : fastApp f n = f n := rfl

-- A `[defeq]` lemma fires unconditionally; the trace is *not* emitted (the
-- trace is specifically for `[backward_defeq]`-only lemmas).
set_option trace.Meta.Tactic.simp.backwardDefEq true in
example (n : Nat) : fastApp Nat.succ n = Nat.succ n := by dsimp only [fastApp_eq]
