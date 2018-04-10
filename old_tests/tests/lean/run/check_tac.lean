open tactic

example (a b : nat) : true :=
begin
  type_check a + 1,
  (do let e : expr := expr.const `bor [],
      let one : expr := `(1 : nat),
      let t  := e one one,
      trace t,
      fail_if_success (type_check t)),
  constructor
end
