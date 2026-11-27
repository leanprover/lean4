import Lean
/-!
The equations of a `match` with many `String` literals prove that two literals are different by
comparing their codes with `String.Internal.ne_of_byteCode`. The code of each literal of the matcher
is computed once, in an auxiliary theorem `strLitCodes`, and shared by all the equations (#16313).
-/
open Lean Meta

/-- Returns the statement of the theorem with the codes of the `String` literals of `matcherName`. -/
def strLitCodes? (matcherName : Name) : MetaM (Option Expr) := do
  discard <| Match.genMatchCongrEqns matcherName
  let name := mkPrivateName (← getEnv) matcherName ++ `strLitCodes
  let some (.thmInfo info) := (← getEnv).find? name | return none
  return some info.type

/-- Returns the conjuncts of `e`. -/
partial def conjuncts (e : Expr) : Array Expr :=
  match_expr e with
  | And a b => #[a] ++ conjuncts b
  | _ => #[e]

/-- Returns the number of occurrences of the constant `declName` in `e`. -/
partial def numOccs (declName : Name) (e : Expr) : Nat :=
  match e with
  | .const n _ => if n == declName then 1 else 0
  | .app f a => numOccs declName f + numOccs declName a
  | .lam _ d b _ | .forallE _ d b _ => numOccs declName d + numOccs declName b
  | .letE _ t v b _ => numOccs declName t + numOccs declName v + numOccs declName b
  | .mdata _ b | .proj _ _ b => numOccs declName b
  | _ => 0

/--
Returns, for each congruence equation of `matcherName`, the number of disequalities between
literals proved by comparing codes, and by comparing bytes.
-/
def numNeProofs (matcherName : Name) : MetaM (Array (Nat × Nat)) := do
  (← Match.genMatchCongrEqns matcherName).mapM fun eqn => do
    let some (.thmInfo info) := (← getEnv).find? eqn | throwError "theorem expected: {eqn}"
    return (numOccs ``String.Internal.ne_of_byteCode info.value, numOccs ``String.Internal.ne_of_sameByteAt info.value)

/-! A matcher with 32 literals. The equation of the literal `i` skips `i` tests. -/

def f : String → Nat
  | "lit_0" => 0 | "lit_1" => 1 | "lit_2" => 2 | "lit_3" => 3
  | "lit_4" => 4 | "lit_5" => 5 | "lit_6" => 6 | "lit_7" => 7
  | "lit_8" => 8 | "lit_9" => 9 | "lit_10" => 10 | "lit_11" => 11
  | "lit_12" => 12 | "lit_13" => 13 | "lit_14" => 14 | "lit_15" => 15
  | "lit_16" => 16 | "lit_17" => 17 | "lit_18" => 18 | "lit_19" => 19
  | "lit_20" => 20 | "lit_21" => 21 | "lit_22" => 22 | "lit_23" => 23
  | "lit_24" => 24 | "lit_25" => 25 | "lit_26" => 26 | "lit_27" => 27
  | "lit_28" => 28 | "lit_29" => 29 | "lit_30" => 30 | "lit_31" => 31
  | _ => 32

/--
info: 32
---
info: String.Internal.byteCode "lit_0" = 215398365661
---
info: String.Internal.byteCode "lit_1" = 219760836062
---
info: String.Internal.byteCode "lit_31" = 56286230429714
-/
#guard_msgs in
run_meta do
  let some type ← strLitCodes? ``f.match_1 | throwError "theorem expected"
  let facts := conjuncts type
  logInfo m!"{facts.size}"
  for i in [0, 1, 31] do logInfo facts[i]!

run_meta do
  let ns ← numNeProofs ``f.match_1
  for i in [0:32] do
    unless ns[i]! == (i, 0) do throwError "unexpected proof for alternative {i}: {ns[i]!}"

example : f "lit_0" = 0 := by simp [f]
example : f "lit_17" = 17 := by simp [f]
example : f "lit_31" = 31 := by simp [f]
example : f "lit_32" = 32 := by simp [f]

/-!
Literals with the same characters at the same positions but different lengths, the empty string,
and the character with code `0`. The code of a literal is different from the code of its prefixes.
-/

def special : String → Nat
  | "" => 0 | "\x00" => 1 | "\x00\x00" => 2 | "a" => 3
  | "ab" => 4 | "abc" => 5 | "αβ" => 6 | "s0" => 7
  | "s1" => 8 | "s2" => 9 | "s3" => 10 | "s4" => 11
  | "s5" => 12 | "s6" => 13 | "s7" => 14 | "s8" => 15
  | "s9" => 16 | "s10" => 17 | "s11" => 18 | "s12" => 19
  | "s13" => 20 | "s14" => 21 | "s15" => 22 | "s16" => 23
  | "s17" => 24 | "s18" => 25 | "s19" => 26 | "s20" => 27
  | "s21" => 28 | "s22" => 29 | "s23" => 30 | "s24" => 31
  | _ => 32

/--
info: String.Internal.byteCode "" = 0
---
info: String.Internal.byteCode "\x00" = 1
---
info: String.Internal.byteCode "\x00\x00" = 258
---
info: String.Internal.byteCode "a" = 98
---
info: String.Internal.byteCode "ab" = 25541
---
info: String.Internal.byteCode "abc" = 6630441
---
info: String.Internal.byteCode "αβ" = 3052170243
-/
#guard_msgs in
run_meta do
  let some type ← strLitCodes? ``special.match_1 | throwError "theorem expected"
  for fact in (conjuncts type)[*...7] do logInfo fact

example : special "" = 0 := by simp [special]
example : special "\x00" = 1 := by simp [special]
example : special "\x00\x00" = 2 := by simp [special]
example : special "ab" = 4 := by simp [special]
example : special "abc" = 5 := by simp [special]
example : special "αβ" = 6 := by simp [special]
example : special "abcd" = 32 := by simp [special]

/-!
A literal with more than 256 bytes does not have a code: the kernel would need a time
quadratic in its length to compute it. A disequality with this literal compares bytes.
-/

def long : String → Nat
  | "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" => 100
  | "lit_0" => 0 | "lit_1" => 1 | "lit_2" => 2 | "lit_3" => 3
  | "lit_4" => 4 | "lit_5" => 5 | "lit_6" => 6 | "lit_7" => 7
  | "lit_8" => 8 | "lit_9" => 9 | "lit_10" => 10 | "lit_11" => 11
  | "lit_12" => 12 | "lit_13" => 13 | "lit_14" => 14 | "lit_15" => 15
  | "lit_16" => 16 | "lit_17" => 17 | "lit_18" => 18 | "lit_19" => 19
  | "lit_20" => 20 | "lit_21" => 21 | "lit_22" => 22 | "lit_23" => 23
  | "lit_24" => 24 | "lit_25" => 25 | "lit_26" => 26 | "lit_27" => 27
  | "lit_28" => 28 | "lit_29" => 29 | "lit_30" => 30 | "lit_31" => 31
  | _ => 32

/-- info: 32 -/
#guard_msgs in
run_meta do
  let some type ← strLitCodes? ``long.match_1 | throwError "theorem expected"
  logInfo m!"{(conjuncts type).size}"

run_meta do
  let ns ← numNeProofs ``long.match_1
  for i in [0:32] do
    -- The test for the long literal is the first one.
    unless ns[i+1]! == (i, 1) do throwError "unexpected proof for alternative {i+1}: {ns[i+1]!}"

example : long "lit_3" = 3 := by simp [long]

/-! A matcher with less than 32 literals does not have the auxiliary theorem. -/

def small : String → Nat
  | "a" => 0
  | "b" => 1
  | "c" => 2
  | _ => 3

/-- info: (none, [(0, 0), (0, 1), (0, 2), (0, 0)]) -/
#guard_msgs in
run_meta do
  logInfo m!"{((← strLitCodes? ``small.match_1).map fun _ => (), ← numNeProofs ``small.match_1)}"
