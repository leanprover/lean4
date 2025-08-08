set_option trace.Elab true

axiom A : Prop

-- @[simp] def Foo.T := True
-- @[simp] def Bar.T := True



-- namespace ex0
-- @[local simp] axiom a : A ↔ True
-- axiom  b : A ↔ True
-- example : A := by simp
-- end ex0


namespace ex1
@[local simp] axiom test.a : A ↔ True
axiom test.b : A ↔ True
@[local simp] axiom c : A ↔ True



-- section ex4
--   axiom b : A ↔ True
-- end ex4
