import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Lean.Data.Json
import Lean

def test (s : String) : String :=
match Lean.Json.parse s with
| Except.ok res    => toString res
| Except.error err => err

#eval test "null"
#eval test "false"
#eval test "true"
#eval test "123.456e-7"
#eval test "123.456e+7"
#eval test "-0.01e8"
#eval test "\"\""
#eval test "\"abc\""
#eval test "[true, 123, \"foo\", []]"
#eval test "{\"a\": 1.2, \"b\": \"foo\", \"c\": null, \"d\": {\"foo\": \"bar\"}, \"e\": [{}]}"
#eval test "[false_]"
#eval test "["
#eval test "]"
#eval test "{"
#eval test "\""
#eval test "1."
#eval test "{foo: 1}"
#eval test "   "
#eval toString (Lean.Json.num ⟨20, 1⟩)
#eval toString (Lean.Json.num ⟨-20, 1⟩)
#eval toString (Lean.Json.num 0.1)
#eval toString (Lean.Json.num <| -0.1)
#eval toString (Lean.Json.num <| -0.01e8)
#eval toString (Lean.Json.num <| 123.456e-7)
#eval 123.456e-7 == Lean.JsonNumber.toFloat 123.456e-7
#eval -123.456e-7 == Lean.JsonNumber.toFloat (-123.456e-7)
#eval 123.456e20 == Lean.JsonNumber.toFloat 123.456e20
#eval 0.0 == Lean.JsonNumber.toFloat 0

open Lean Json

def floatRoundtrip (x : Float) : CoreM Unit := do
  let j := x |> toJson
  let y ← j |> fromJson? (α := Float) |> ofExcept
  dbg_trace "{y}"
  if y.isNaN && x.isNaN then
    -- [note] NaN ≠ NaN
    return ()
  if y != x then
    throwError "failure {x} → {j} → {y}"
  return ()

#eval floatRoundtrip 0.0
#eval floatRoundtrip (-0.0)
#eval floatRoundtrip 1.0
#eval floatRoundtrip (-1.0)
#eval floatRoundtrip (1e100)
#eval floatRoundtrip (123456789e-6)
#eval floatRoundtrip (0.0 / 0.0)
#eval floatRoundtrip (1.0 / 0.0)
#eval floatRoundtrip (-1.0 / 0.0)
