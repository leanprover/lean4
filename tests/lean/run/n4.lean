definition Bool [inline] : Type.{1} := Type.{0}
section
  variable N : Type.{1}
  variables a b c : N
  variable and : Bool → Bool → Bool
  infixr `∧` 35 := and
  variable le : N → N → Bool
  variable lt : N → N → Bool
  precedence `≤`:50
  precedence `<`:50
  infixl ≤ := le
  infixl < := lt
  check a ≤ b
  definition T : Bool := a ≤ b
  check T
end
check T
(*
print(get_env():find("T"):value())
*)