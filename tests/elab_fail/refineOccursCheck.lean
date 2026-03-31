theorem ex1 : True := by
  refine ?a
  refine ?a
  refine ?a
  exact True.intro

axiom ax.{u} {α : Sort u} (a : α) : α

theorem ex2 : True := by
  refine ?a
  refine ax ?a -- Error trying to assign `?a := ax ?a`
