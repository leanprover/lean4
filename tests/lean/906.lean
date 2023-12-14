-- Print a nat using well-founded recursion
def natPrintAux (n : Nat) (sink : List Char) : List Char :=
  if h0 : n < 10
  then (n.digitChar :: sink)
  else natPrintAux (n / 10) (Nat.digitChar (n % 10) :: sink)
termination_by _ n => n
decreasing_by sorry

set_option maxRecDepth 100  -- default takes ages in debug mode and triggers stack space threshold

-- I meant to write `simp only [natPrintAux]`, but accidentally referenced the current theorem
theorem natPrintAux_eq (n : Nat) (sink : List Char) :
        natPrintAux n sink = if n < 10 then (n.digitChar :: sink) else natPrintAux (n / 10) (Nat.digitChar (n % 10) :: sink) := by
  simp only [natPrintAux_eq]
