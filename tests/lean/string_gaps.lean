import Lean

#eval "a\
b"
#eval "a\
       b"
#eval "a \
       b"
#eval "a \
         \
         \
         b"
#eval "this is \
       a string"
#eval "this is \
        a string"
#eval "there are three spaces between the brackets <   \
                         >"
#eval "there are three spaces between the brackets <\
         \x20  >"
#eval "this is\
       \n  a string with two space indent"

#eval s!"a\
b"
#eval s!"a\
         b"
#eval s!"a\
         b"
#eval s!"a\
         {"b"}\
        "

open Lean

#eval show MetaM String from do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term "\"a\\\n b\""
  let some s := stx.isStrLit? | failure
  return s

#eval show MetaM String from do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term "\"a\\\r\n b\""
  let some s := stx.isStrLit? | failure
  return s

#eval show MetaM String from do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term "\"a\\\r b\""
  let some s := stx.isStrLit? | failure
  return s

#eval show MetaM String from do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term "\"a\\ b\""
  let some s := stx.isStrLit? | failure
  return s

-- Scala-style stripMargin
def String.dedent (s : String) : Option String :=
  let parts := s.split (· == '\n') |>.map String.trimLeft
  match parts with
  | [] => ""
  | [p] => p
  | p₀ :: parts =>
    if !parts.all (·.startsWith "|") then
      none
    else
      p₀ ++ "\n" ++ String.intercalate "\n" (parts.map fun p => p.drop 1)

elab "d!" s:str : term => do
  let some s := s.raw.isStrLit? | Lean.Elab.throwIllFormedSyntax
  let some s := String.dedent s | Lean.Elab.throwIllFormedSyntax
  pure $ Lean.mkStrLit s

#eval d!"this is \
            line 1
        |  line 2, indented
        |line 3"
