import LeanExport.Parse
import Lean.Data.Json.Printer

/-!
Tests that the `LeanExport` NDJSON reader rejects malformed lines: trailing bytes after the JSON
object, objects with duplicate keys, and an index of a name, level or expression that is bound
twice.
-/

def parse (lines : List String) : IO Unit := do
  let input := String.intercalate "\n" ("{}" :: lines) ++ "\n"
  let buf ← IO.mkRef { data := input.toUTF8 : IO.FS.Stream.Buffer }
  let env ← LeanExport.parseStream (.ofBuffer buf)
  IO.println s!"ok: {env.constOrder}"

/-- info: ok: #[] -/
#guard_msgs in
#eval parse [
  "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}",
  "{\"il\":1,\"succ\":0}",
  "{\"ie\":0,\"sort\":1}"]

/-- info: ok: #[a] -/
#guard_msgs in
#eval parse [
  "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}",
  "{\"il\":1,\"succ\":0}",
  "{\"ie\":0,\"sort\":1}",
  "{\"axiom\":{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}"]

-- Trailing bytes after the object

/-- error: Invalid JSON: offset 35: expected end of input -/
#guard_msgs in
#eval parse ["{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}} x"]

/-- error: Invalid JSON: offset 34: expected end of input -/
#guard_msgs in
#eval parse ["{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}{\"in\":2,\"str\":{\"pre\":0,\"str\":\"b\"}}"]

-- Duplicate object keys

/-- error: Invalid JSON: offset 12: duplicate object key "in" -/
#guard_msgs in
#eval parse ["{\"in\":1,\"in\":2,\"str\":{\"pre\":0,\"str\":\"a\"}}"]

/-- error: Invalid JSON: offset 28: duplicate object key "pre" -/
#guard_msgs in
#eval parse ["{\"in\":1,\"str\":{\"pre\":0,\"pre\":1,\"str\":\"a\"}}"]

-- Keys are compared after unescaping.
/-- error: Invalid JSON: offset 33: duplicate object key "pre" -/
#guard_msgs in
#eval parse ["{\"in\":1,\"str\":{\"pre\":0,\"\\u0070re\":1,\"str\":\"a\"}}"]

-- `Lean.Json.parse` itself is unchanged.
/-- info: some "{\"a\": 2}" -/
#guard_msgs in
#eval toString <$> (Lean.Json.parse "{\"a\": 1, \"a\": 2}").toOption

-- Indices bound twice

/-- error: Name index 0 bound twice -/
#guard_msgs in
#eval parse ["{\"in\":0,\"str\":{\"pre\":0,\"str\":\"a\"}}"]

/-- error: Name index 1 bound twice -/
#guard_msgs in
#eval parse [
  "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}",
  "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"b\"}}"]

/-- error: Level index 0 bound twice -/
#guard_msgs in
#eval parse ["{\"il\":0,\"succ\":0}"]

/-- error: Level index 1 bound twice -/
#guard_msgs in
#eval parse [
  "{\"il\":1,\"succ\":0}",
  "{\"il\":1,\"succ\":1}"]

/-- error: Expr index 0 bound twice -/
#guard_msgs in
#eval parse [
  "{\"ie\":0,\"bvar\":0}",
  "{\"ie\":0,\"bvar\":1}"]
