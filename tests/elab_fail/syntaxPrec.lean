syntax "foo" term <|> "bar" term : term  -- should not compile
set_option trace.Elab.command true
syntax "foo" ("*" <|> term,+) : term
