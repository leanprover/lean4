import Lean.Data.Json

/-! Large JSON exponents must not panic (#13987). -/

/-- info: err offset 12: exp too large -/
#guard_msgs in
#eval show IO Unit from do
  match Lean.Json.parse "3E9999999993" with
  | .ok _ => IO.println "ok"
  | .error e => IO.println s!"err {e}"

/-- info: err offset 31: exp too large -/
#guard_msgs in
#eval show IO Unit from do
  match Lean.Json.parse "3E99999999999999999999999999999" with
  | .ok _ => IO.println "ok"
  | .error e => IO.println s!"err {e}"

/-- info: ok -/
#guard_msgs in
#eval show IO Unit from do
  match Lean.Json.parse "3E100" with
  | .ok _ => IO.println "ok"
  | .error e => IO.println s!"err {e}"
