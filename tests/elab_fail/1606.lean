example : True := by
  skip
    skip --< should complain about misleading indentation
  trivial

macro "frobnicate" : tactic => `(tactic| skip)

example : True := by
  conv =>
    skip
    frobnicate --< should not parse frobnicate as a tactic
  trivial

-- check error message without default handler for conv tactics
declare_syntax_cat item
syntax "valid_item" : item
macro "block" "=>" sepByIndentSemicolon(item) : tactic => `(tactic| skip)

example : True := by
  block =>
    valid_item
    frobnicate --< should not parse frobnicate as a tactic
