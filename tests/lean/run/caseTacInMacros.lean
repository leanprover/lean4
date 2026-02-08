def f (n : Nat) := n + 1

macro "mymacro1 " h:ident : tactic =>
  `(tactic| {
      cases $h:ident with
      | zero => decide
      | succ => simp +arith [f]
  })

example : f n > 0 := by
  mymacro1 n -- works

macro "mymacro2 " h:ident : tactic =>
  `(tactic| {
      cases $h:ident
      case zero => decide
      case succ => simp +arith [f]
  })

example : f n > 0 := by
  -- Should **not** generate: Case tag 'zero._@.cases3._hyg.747' not found.
  mymacro2 n
