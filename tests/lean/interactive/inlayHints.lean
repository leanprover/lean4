inductive Foo (x : α) : β → β → Prop where
  | foo : Foo x a a

structure Bar (x : α) where
  bar (a : α) (b : β) : γ → Bar x

def f (a : α) : β := sorry

variable (f : Foo x b b) in
theorem g (_ : α) : n = 0 := sorry

example : α → α := id

axiom refl : x = x

--^ collectDiagnostics
--^ inlayHints
