section
  parameters {b c : bool}

  definition R : Prop := (b = c)

  parameters (b c)
  definition R2 := R
  parameter (c)
  parameter (b)
  definition R3 := R
  parameter {c}
  parameter (b)
  definition R4 := R
  parameters {c b}
  definition R5 := R
  parameters (c)
  definition R6 := R
end

check @R
check @R2
check @R3
check @R4
check @R5
check @R6
