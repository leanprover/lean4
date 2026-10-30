import Lean.Data.Json
open Lean

/-!
Regression test for #15993: `Json.parse` recursed once per level of nesting without a limit, so
deeply nested input overflowed the stack and aborted the process.  It now fails past
`Json.Parser.maxDepth` levels.
-/

def nestedArrays (n : Nat) : String :=
  String.ofList (List.replicate n '[') ++ String.ofList (List.replicate n ']')

def nestedObjects (n : Nat) : String :=
  String.join (List.replicate n "{\"a\":") ++ "1" ++ String.ofList (List.replicate n '}')

/-- Arrays and objects alternating, `n` levels deep. -/
def nestedMixed : Nat → String
  | 0 => "1"
  | n + 1 => if n % 2 == 0 then "[" ++ nestedMixed n ++ "]" else "{\"a\":" ++ nestedMixed n ++ "}"

#guard (Json.parse (nestedArrays Json.Parser.maxDepth)).toOption.isSome
#guard (Json.parse (nestedObjects Json.Parser.maxDepth)).toOption.isSome
#guard (Json.parse (nestedArrays (Json.Parser.maxDepth + 1))).toOption.isNone
#guard (Json.parse (nestedObjects (Json.Parser.maxDepth + 1))).toOption.isNone
#guard (Json.parse (nestedMixed Json.Parser.maxDepth)).toOption.isSome
#guard (Json.parse (nestedMixed (Json.Parser.maxDepth + 1))).toOption.isNone

/-- error: offset 10000: nesting deeper than 10000 levels -/
#guard_msgs in
#eval IO.ofExcept (Json.parse (nestedArrays (10 * Json.Parser.maxDepth)))
