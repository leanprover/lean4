import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

def test (s : String) : String :=
match Lean.Json.parse s with
| Except.ok res    => toString res
| Except.error err => err

#eval test "null"
#eval test "false"
#eval test "true"
#eval test "123.456e-7"
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
