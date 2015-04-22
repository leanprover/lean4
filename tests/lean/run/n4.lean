prelude
definition Prop : Type.{1} := Type.{0}
section
  variable N : Type.{1}
  variables a b c : N
  variable and : Prop → Prop → Prop
  local infixr `∧`:35 := and
  variable le : N → N → Prop
  variable lt : N → N → Prop
  precedence `≤`:50
  precedence `<`:50
  local infixl ≤ := le
  local infixl < := lt
  check a ≤ b
  definition T : Prop := a ≤ b
  check T
end
check T
(*
print(get_env():find("T"):value())
*)
