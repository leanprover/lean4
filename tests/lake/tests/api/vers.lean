import Lake.Util.Version

open Lake

def failParse (ver : String) : IO Unit :=  do
  let ver ← IO.ofExcept <| VerRange.parse ver
  let actual := (VerRange.ofClauses ver.clauses).toString
  throw <| IO.userError s!"unexpected parse: {actual}"

def checkParse (ver expected : String) : IO Unit :=  do
  let ver ← IO.ofExcept <| VerRange.parse ver
  let actual := (VerRange.ofClauses ver.clauses).toString
  unless actual == expected do throw <| IO.userError s!"unexpected parse: {actual}"

def checkMatch (range : String) (accepts rejects : Array String) : IO Unit :=  do
  let range ← IO.ofExcept <| VerRange.parse range
  accepts.forM fun s => do
    let ver ← IO.ofExcept <| StdVer.parse s
    unless range.test ver do throw <| IO.userError s!"unexpected rejection: {s}"
  rejects.forM fun s => do
    let ver ← IO.ofExcept <| StdVer.parse s
    if range.test ver then throw <| IO.userError s!"unexpected accept: {s}"

/-! ## Comparators -/

#eval checkParse "<1.2.3"   "<1.2.3"
#eval checkParse "<=1.2.3"  "≤1.2.3"
#eval checkParse "≤1.2.3"   "≤1.2.3"
#eval checkParse ">1.2.3"   ">1.2.3"
#eval checkParse ">=1.2.3"  "≥1.2.3"
#eval checkParse "≥1.2.3"   "≥1.2.3"
#eval checkParse "=1.2.3"   "=1.2.3"
#eval checkParse "!=1.2.3"  "≠1.2.3"
#eval checkParse "≠1.2.3"   "≠1.2.3"

#eval checkMatch "<1.2.3"   #["1.0.0"] #["1.2.3", "2.0.0"]
#eval checkMatch "≤1.2.3"   #["1.0.0", "1.2.3"] #["2.0.0"]
#eval checkMatch ">1.2.3"   #["2.0.0"] #["1.2.3", "1.0.0"]
#eval checkMatch "≥1.2.3"   #["2.0.0", "1.2.3"] #["1.0.0"]
#eval checkMatch "=1.2.3"   #["1.2.3"] #["1.0.0", "2.0.0"]
#eval checkMatch "≠1.2.3"   #["1.0.0", "2.0.0"] #["1.2.3"]

/-! ## Clauses -/

#eval checkParse "≥1.2.7, <1.3.0" "≥1.2.7, <1.3.0"
#eval checkParse "=1.2.7 || ≥1.2.9 <2.0.0" "=1.2.7 || ≥1.2.9, <2.0.0"

#eval checkMatch "≥1.2.7, <1.3.0"
  #["1.2.7", "1.2.8", "1.2.99"] #["1.2.6", "1.3.0", "1.1.0"]

#eval checkMatch "=1.2.7 || ≥1.2.9 <2.0.0"
  #["1.2.7", "1.2.9", "1.4.6"] #["1.2.8", "2.0.0"]

/-! ## Bare Versions  -/
-- TODO: futher consider behavior here

#eval checkParse "1"        "≥1.0.0, <2.0.0"
#eval checkParse "1.2"      "≥1.2.0, <1.3.0"
#eval checkParse "1.2.3"    "=1.2.3"

/-- error: expected version range -/
#guard_msgs in #eval failParse ""

/-! ## Tilde Ranges

Lake follows Node's behavior rather than Rust's for 3-component tilde versions.

https://github.com/npm/node-semver/tree/v7.7.3?tab=readme-ov-file#tilde-ranges-123-12-1
https://doc.rust-lang.org/stable/cargo/reference/specifying-dependencies.html?highlight=caret#tilde-requirements
-/

#eval checkParse "~1"       "≥1.0.0, <2.0.0"
#eval checkParse "~1.2"     "≥1.2.0, <1.3.0"
#eval checkParse "~1.2.3"   "≥1.2.3, <1.3.0"

#eval checkParse "~0"       "≥0.0.0, <1.0.0"
#eval checkParse "~0.2"     "≥0.2.0, <0.3.0"
#eval checkParse "~0.2.3"   "≥0.2.3, <0.3.0"

/-! ## Wildcard Ranges

Lake supports both the `*` (Rust and Node) and the `x`/`X` (Node) form of wildcard versions.

https://github.com/npm/node-semver/tree/v7.7.3?tab=readme-ov-file#x-ranges-12x-1x-12-
https://doc.rust-lang.org/stable/cargo/reference/specifying-dependencies.html?highlight=caret#wildcard-requirements
-/

#eval checkParse "*"        "≥0.0.0"
#eval checkParse "x"        "≥0.0.0"
#eval checkParse "X"        "≥0.0.0"
#eval checkParse "x.*"      "≥0.0.0"
#eval checkParse "x.*.X"    "≥0.0.0"

#eval checkParse "1.x"      "≥1.0.0, <2.0.0"
#eval checkParse "1.X"      "≥1.0.0, <2.0.0"
#eval checkParse "1.*"      "≥1.0.0, <2.0.0"
#eval checkParse "1.x.X"    "≥1.0.0, <2.0.0"
#eval checkParse "1.*.*"    "≥1.0.0, <2.0.0"

#eval checkParse "1.2.*"    "≥1.2.0, <1.3.0"
#eval checkParse "1.2.x"    "≥1.2.0, <1.3.0"
#eval checkParse "1.2.X"    "≥1.2.0, <1.3.0"
