import Lake.Util.Version

open Lake

def runParse (ver : String) : IO String :=  do
  let ver ← IO.ofExcept <| VerRange.parse ver
  return (VerRange.ofClauses ver.clauses).toString

def checkParse (ver expected : String) : IO Unit :=  do
  let ver ← IO.ofExcept <| VerRange.parse ver
  let actual := (VerRange.ofClauses ver.clauses).toString
  unless actual == expected do
    throw <| IO.userError s!"incorrect parse: expected\n  '{expected}'\ngot\n  '{actual}'"

def checkMatch (range : String) (accepts rejects : Array String) : IO Unit :=  do
  let range ← IO.ofExcept <| VerRange.parse range
  accepts.forM fun s => do
    let ver ← IO.ofExcept <| StdVer.parse s
    unless range.test ver do
      throw <| IO.userError s!"invalid reject: expected\n  '{range}'\nto accept\n  '{s}'"
  rejects.forM fun s => do
    let ver ← IO.ofExcept <| StdVer.parse s
    if range.test ver then
      throw <| IO.userError s!"invalid accept: expected\n  '{range}'\nto reject\n  '{s}'"

/-!
## Comparators

Lake supports the comparison operators available in Rust and Node with
the addition of unicode alternatives and the `!=`/`≠` operator.

https://github.com/npm/node-semver/tree/v7.7.3?tab=readme-ov-file#ranges
https://doc.rust-lang.org/stable/cargo/reference/specifying-dependencies.html#comparison-requirements
-/

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

#eval checkMatch "<1.2.3-beta.2"
  #["1.2.3-alpha.3", "1.2.3-beta.1"]
  #["1.2.3", "1.2.3-beta.7", "1.2.3-beta.2", "1.2.3-gamma.7", "1.0.0-pre"]
#eval checkMatch "≤1.2.3-beta.2"
  #["1.2.3-alpha.3", "1.2.3-beta.1", "1.2.3-beta.2"]
  #["1.0.0-pre",  "1.2.3-beta.7", "1.2.3-gamma.7", "1.2.3"]
#eval checkMatch ">1.2.3-beta.2"
  #["1.2.3-beta.7", "1.2.3-gamma.7", "1.2.3"]
  #["1.2.3-alpha.2", "1.2.3-beta.2", "3.4.5-pre"]
#eval checkMatch "≥1.2.3-beta.2"
  #["1.2.3-beta.2", "1.2.3-beta.7", "1.2.3-gamma.7", "1.2.3"]
  #["1.2.3-alpha.2","3.4.5-pre"]
#eval checkMatch "=1.2.3-beta.2"
  #["1.2.3-beta.2"] #["1.2.3-beta.0", "1.2.3", "3.4.5-pre"]
#eval checkMatch "≠1.2.3-beta.2"
  #["1.2.3-beta.0", "1.2.3"] #["1.0.0-pre", "1.2.3-beta.2", "3.4.5-pre"]

#eval checkMatch "<1.2.3-"
  #["1.0.0-alpha.9", "1.2.3-alpha.1"] #["1.2.3", "1.2.4-beta.2"]

/-- error: invalid version core: incorrect number of components: got 2, expected 3 -/
#guard_msgs in #eval runParse ">1.2"

/-!
## Clauses

Lake supports
* OR clauses: Node-style `||`
* AND clauses: Rust-style `,` and Node-style juxtaposition

https://github.com/npm/node-semver/tree/v7.7.3?tab=readme-ov-file#ranges
https://doc.rust-lang.org/stable/cargo/reference/specifying-dependencies.html#multiple-version-requirements
-/

#eval checkParse "≥1.2.7, <1.3.0" "≥1.2.7, <1.3.0"
#eval checkParse "=1.2.7 || ≥1.2.9 <2.0.0" "=1.2.7 || ≥1.2.9, <2.0.0"

#eval checkMatch "≥1.2.7, <1.3.0"
  #["1.2.7", "1.2.8", "1.2.99"] #["1.2.6", "1.3.0", "1.1.0"]

#eval checkMatch "=1.2.7 || ≥1.2.9 <2.0.0"
  #["1.2.7", "1.2.9", "1.4.6"] #["1.2.8", "2.0.0"]

/-!
## Bare Versions

Lake bans these.

https://github.com/npm/node-semver/tree/v7.7.3?tab=readme-ov-file#x-ranges-12x-1x-12-
https://doc.rust-lang.org/stable/cargo/reference/specifying-dependencies.html#default-requirements
-/

/-- error: expected version range -/
#guard_msgs in #eval runParse ""

/--
error: invalid version range: bare versions are not supported;
if you want to pin a specific version, use '=' before the full version;
otherwise, use '≥' to support it and future versions
-/
#guard_msgs in #eval runParse "1"

/--
error: invalid version range: bare versions are not supported;
if you want to pin a specific version, use '=' before the full version;
otherwise, use '≥' to support it and future versions
-/
#guard_msgs in #eval runParse "1.2"

/--
error: invalid version range: bare versions are not supported;
if you want to pin a specific version, use '=' before the full version;
otherwise, use '≥' to support it and future versions
-/
#guard_msgs in #eval runParse "1.2.3"

/-! ## Caret Ranges

Lake follows Node's and Rust's behavior for caret ranges.

https://github.com/npm/node-semver/tree/v7.7.3?tab=readme-ov-file#caret-ranges-123-025-004
https://doc.rust-lang.org/stable/cargo/reference/specifying-dependencies.html#caret-requirements
-/

#eval checkParse "^1"       "≥1.0.0, <2.0.0-"
#eval checkParse "^1.2"     "≥1.2.0, <2.0.0-"
#eval checkParse "^1.2.3"   "≥1.2.3, <2.0.0-"

#eval checkParse "^0.2"     "≥0.2.0, <0.3.0-"
#eval checkParse "^0.2.3"   "≥0.2.3, <0.3.0-"
#eval checkParse "^0.0.3"   "≥0.0.3, <0.0.4-"

#eval checkParse "^0"       "≥0.0.0, <1.0.0-"
#eval checkParse "^0.0"     "≥0.0.0, <0.1.0-"

#eval checkParse "^1-beta.2"      "≥1.0.0-beta.2, <2.0.0-"
#eval checkParse "^1.2-beta.2"    "≥1.2.0-beta.2, <2.0.0-"
#eval checkParse "^1.2.3-beta.2"  "≥1.2.3-beta.2, <2.0.0-"
#eval checkParse "^0.0.0-beta.2"  "≥0.0.0-beta.2, <0.0.1-"

/-- error: invalid major version: expected numeral, got '' -/
#guard_msgs in #eval runParse "^"

/-- error: invalid version: '-' suffix cannot be empty -/
#guard_msgs in #eval runParse "^1.2.3-"

/-- error: invalid caret range: incorrect number of components: got 4, expected 1-3 -/
#guard_msgs in #eval runParse "^1.2.3.4"

/-- error: invalid caret range: `^0.0.0` is degenerate; use `=0.0.0` instead -/
#guard_msgs in #eval runParse "^0.0.0"

/-! ## Tilde Ranges

Lake follows Node's and Rust's behavior for tilde ranges.

https://github.com/npm/node-semver/tree/v7.7.3?tab=readme-ov-file#tilde-ranges-123-12-1
https://doc.rust-lang.org/stable/cargo/reference/specifying-dependencies.html#tilde-requirements
-/

#eval checkParse "~1"       "≥1.0.0, <2.0.0-"
#eval checkParse "~1.2"     "≥1.2.0, <1.3.0-"
#eval checkParse "~1.2.3"   "≥1.2.3, <1.3.0-"

#eval checkParse "~0.2"     "≥0.2.0, <0.3.0-"
#eval checkParse "~0.2.3"   "≥0.2.3, <0.3.0-"
#eval checkParse "~0.0.3"   "≥0.0.3, <0.1.0-"

#eval checkParse "~0"       "≥0.0.0, <1.0.0-"
#eval checkParse "~0.0"     "≥0.0.0, <0.1.0-"
#eval checkParse "~0.0.0"   "≥0.0.0, <0.1.0-"

#eval checkParse "~1-beta.2"      "≥1.0.0-beta.2, <2.0.0-"
#eval checkParse "~1.2-beta.2"    "≥1.2.0-beta.2, <1.3.0-"
#eval checkParse "~1.2.3-beta.2"  "≥1.2.3-beta.2, <1.3.0-"

#eval checkMatch "~1.2.3-beta.2"
  #["1.2.3-beta.2", "1.2.3-beta.7", "1.2.3", "1.2.7"]
  #["1.2.1", "1.2.3-alpha.3", "1.2.3-beta.1"]

/-- error: invalid major version: expected numeral, got '' -/
#guard_msgs in #eval runParse "~"

/-- error: invalid version: '-' suffix cannot be empty -/
#guard_msgs in #eval runParse "~1.2.3-"

/-- error: invalid tilde range: incorrect number of components: got 4, expected 1-3 -/
#guard_msgs in #eval runParse "~1.2.3.4"

/-! ## Wildcard Ranges

Lake supports both the `*` (Rust and Node) and the `x`/`X` (Node) form of wildcard versions.

https://github.com/npm/node-semver/tree/v7.7.3?tab=readme-ov-file#x-ranges-12x-1x-12-
https://doc.rust-lang.org/stable/cargo/reference/specifying-dependencies.html#wildcard-requirements
-/

#eval checkParse "*"        "≥0.0.0"
#eval checkParse "x"        "≥0.0.0"
#eval checkParse "X"        "≥0.0.0"
#eval checkParse "x.*"      "≥0.0.0"
#eval checkParse "x.*.X"    "≥0.0.0"

#eval checkParse "1.x"      "≥1.0.0, <2.0.0-"
#eval checkParse "1.X"      "≥1.0.0, <2.0.0-"
#eval checkParse "1.*"      "≥1.0.0, <2.0.0-"
#eval checkParse "1.x.X"    "≥1.0.0, <2.0.0-"
#eval checkParse "1.*.*"    "≥1.0.0, <2.0.0-"

#eval checkParse "1.2.*"    "≥1.2.0, <1.3.0-"
#eval checkParse "1.2.x"    "≥1.2.0, <1.3.0-"
#eval checkParse "1.2.X"    "≥1.2.0, <1.3.0-"

/-! ### Errors -/

/-- error: invalid wildcard range: wildcard versions do not support suffixes -/
#guard_msgs in #eval runParse "1.*.*-*"

/-- error: invalid major version: expected numeral or wildcard, got 'a' -/
#guard_msgs in #eval runParse "a.*.*"

/-- error: invalid minor version: expected numeral or wildcard, got 'b' -/
#guard_msgs in #eval runParse "*.b.*"

/-- error: invalid patch version: expected numeral or wildcard, got 'c' -/
#guard_msgs in #eval runParse "*.*.c"

/-- error: invalid minor version: components after a wildcard must be wildcards -/
#guard_msgs in #eval runParse "*.2.*"

/-- error: invalid patch version: components after a wildcard must be wildcards -/
#guard_msgs in #eval runParse "*.*.3"

/-- error: invalid patch version: components after a wildcard must be wildcards -/
#guard_msgs in #eval runParse "1.*.3"

/-- error: invalid wildcard range: incorrect number of components: got 4, expected 1-3 -/
#guard_msgs in #eval runParse "1.*.*.*"
