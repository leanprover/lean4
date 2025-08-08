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
axiom test.a : A ↔ True
axiom b : A ↔ True
/--
  error: simp made no progress
-/
#guard_msgs in
example : A := by simp -- fails
end ex1


-- section ex4
--   axiom b : A ↔ True
-- end ex4
