/-!
  # More helpful ranges of parser error messages on unexpected tokens

  When the parser hits an unexpected token, it will now include all preceding
  whitespace in the error message range as the expected token could be inserted
  at any of these places to fix the error. -/

/-!
  In the following example, we want the parser error to start right after
  `exact` as the error belongs to this declaration, not the next one, and
  otherwise would be too easy to overlook. -/

theorem lem1 : True := by
  exact

theorem lem2 : True := ⟨⟩

/-!
  Outside of tactics as well it is generally a better idea to place the error
  right after the last correct token. -/

def f1

def f2 := 0

/-!
  We do not currently special-case linebreaks in this; on a single line,
  the shift is usually not very noticeable nor clearly worse than before. -/

def f3 := def f4 := 0

/-! Test other expected token errors as well -/

inductive

example := 0

-- merge of token errors
set_option pp.all

example := 0

/-! Do not shift other kinds of errors. -/

example := "a
