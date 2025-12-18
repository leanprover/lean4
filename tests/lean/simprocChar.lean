example (h : x = 'a') : x = 'A'.toLower := by
  simp
  trace_state
  assumption

example (h : x = 'A') : x = 'a'.toUpper := by
  simp
  trace_state
  assumption

def f (c : Char) := c

example (h : x = 'A') : x = f 'a'.toUpper := by
  simp (config := { ground := true })
  trace_state
  assumption

example (h : x = "a") : x = toString 'a' := by
  simp
  trace_state
  assumption

example (h : x = 65) : x = 'A'.toNat := by
  simp
  trace_state
  assumption

example (h : x = true) : x = ' '.isWhitespace := by
  simp
  trace_state
  assumption

example (h : x = true) : x = 'C'.isAlpha := by
  simp
  trace_state
  assumption

example (h : x = true) : x = '7'.isDigit := by
  simp
  trace_state
  assumption

example (h : x = true) : x = '7'.isAlphanum := by
  simp
  trace_state
  assumption

example (h : x = true) : x = 'a'.isLower := by
  simp
  trace_state
  assumption

example (h : x = true) : x = 'A'.isUpper := by
  simp
  trace_state
  assumption

example (h : x = 65) : x = 'A'.val := by
  simp
  trace_state
  assumption

example (h : x = 'A') : x = Char.ofNatAux 65 (by decide) := by
  simp
  trace_state
  assumption


example (h : x = false) : x = ('a' == 'b') := by
  simp
  trace_state
  assumption

example (h : x = true) : x = ('a' != 'b') := by
  simp
  trace_state
  assumption

example (h : ¬x) : x = ('a' = 'b') := by
  simp
  trace_state
  assumption

example (h : x) : x = ('a' ≠ 'b') := by
  simp
  trace_state
  assumption
