open nat

section
  parameter (A : Type)
  definition f (a b : A) : A := a

  definition add2 (a : nat) : nat := a + 2

  postfix `+.2`:100 := add2

  eval 3 +.2
end

example : 3 +.2 = 5 :=
rfl
