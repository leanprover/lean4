definition Prop : Type.{1} := Type.{0}
context
  parameter N : Type.{1}
  parameters a b c : N
  parameter and : Prop → Prop → Prop
  infixr `∧`:35 := and
  parameter le : N → N → Prop
  parameter lt : N → N → Prop
  precedence `≤`:50
  precedence `<`:50
  infixl ≤ := le
  infixl < := lt
  check a ≤ b
  definition T : Prop := a ≤ b
  check T
end
check T
(*
print(get_env():find("T"):value())
*)
