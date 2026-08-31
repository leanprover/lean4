import Lean.Data.EditDistance

open Lean.EditDistance

/-!
Tests the implementation of Levenshtein distances by constructing a number of strings with known
edit distances (or known bounds), and comparing the results.
-/

def strings := #["", "a", "aa", "ab", "supercalifragilisticexpialidocious", "𝒫(𝒜)"]

/-!
# Infrastructure
-/

structure Stats where
  passed : Nat := 0
  failed : Array (String × String × Nat × Option Nat) := #[]

def report : StateT Stats IO Unit := do
  if (← get).failed.isEmpty then
    IO.println s!"All {(← get).passed} tests passed"
  else
    IO.println s!"While {(← get).passed} tests passed, {(← get).failed.size} failed:"
    for (str, del, expected, actual) in (← get).failed do
      IO.println s!" • {str.quote} and {del.quote}: expected {expected}, got {actual}"

/-!
# Testing Individual Operations

These tests check whether individual operations yield the expected result.
-/

def deletions (n : Nat) (s : String) : Array String :=
  match n with
  | 0 => #[s]
  | n' + 1 => Id.run do
    let mut out := #[]
    for s' in deletions n' s do
      if s'.isEmpty then break
      for i in [0:s'.length] do
        let d := (s'.take i).copy ++ s'.drop (i + 1)
        if !out.contains d then out := out.push d
    return out.reverse

-- Quick check to make sure that the modifications are as expected

/-- info: #["abc", "abd", "acd", "bcd"] -/
#guard_msgs in
#eval deletions 1 "abcd"

/-- info: #["cd", "ad", "bd", "ab", "ac", "bc"] -/
#guard_msgs in
#eval deletions 2 "abcd"

/-- info: #["b", "a", "c", "d"] -/
#guard_msgs in
#eval deletions 3 "abcd"

/-- info: #[""] -/
#guard_msgs in
#eval deletions 4 "abcd"

/-- info: #["aaaa"] -/
#guard_msgs in
#eval deletions 1 "aaaaa"


def testDeletions (s : String) : StateT Stats IO Unit := do
  for i in [0:min s.length 4] do -- This generates O(2^n) tests, so a limit is needed
    let dels := deletions i s
    for del in dels do
      if let some d := levenshtein s del s.length then
        if d != i then
          modify fun st => { st with failed := st.failed.push (s, del, i, some d) }
        else
          modify fun st => { st with passed := st.passed + 1 }
      else
        modify fun st => { st with failed := st.failed.push (s, del, i, none) }

/-- info: All 6566 tests passed -/
#guard_msgs in
#eval show IO Unit from do
  (strings.forM testDeletions *> report).run {} <&> (·.1)

def insertions (toInsert : String) (s : String) : Array String := Id.run do
  let mut out := #[s]
  let mut iter := toInsert.iter
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    let mut next := #[]
    for s' in out do
      for i in [0:s'.length + 1] do
        next := next.push ((s'.take i |>.copy).push c ++ s'.drop i)
    out := next
  return out

/--
info: #["baxyz", "abxyz", "axbyz", "axybz", "axyzb", "bxayz", "xbayz", "xabyz", "xaybz", "xayzb", "bxyaz", "xbyaz", "xybaz",
  "xyabz", "xyazb", "bxyza", "xbyza", "xybza", "xyzba", "xyzab"]
-/
#guard_msgs in
#eval insertions "ab" "xyz"

def testInsertions (s : String) : StateT Stats IO Unit := do
  for i in #["", "X", "ab", "•𝒜▼"] do
    let inss := insertions i s
    for ins in inss do
      if let some d := levenshtein s ins (s.length + i.length) then
        if d != i.length then
          modify fun st => { st with failed := st.failed.push (s, ins, i.length, some d) }
        else
          modify fun st => { st with passed := st.passed + 1 }
      else
        modify fun st => { st with failed := st.failed.push (s, ins, i.length, none) }

/-- info: All 48357 tests passed -/
#guard_msgs in
#eval show IO Unit from do
  (strings.forM testInsertions *> report).run {} <&> (·.1)

def substs (toSubst : String) (s : String) : Array String := Id.run do
  let mut out := #[s]
  let mut iter := toSubst.iter
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    let mut next := #[]
    for s' in out do
      let mut iter2 := s'.iter
      while h2 : iter2.hasNext do
        let c2 := iter2.curr' h2
        let i := iter2.i
        iter2 := iter2.next' h2
        if c ≠ c2 then
          next := next.push <| s'.set i c
    out := next
  return out

/-- info: #[] -/
#guard_msgs in
#eval substs "X" ""

/-- info: #["Xbc", "aXc", "abX"] -/
#guard_msgs in
#eval substs "X" "abc"

/-- info: #["Ybc", "XYc", "XbY", "YXc", "aYc", "aXY", "YbX", "aYX", "abY"] -/
#guard_msgs in
#eval substs "XY" "abc"

def testSubsts (s : String) : StateT Stats IO Unit := do
  for i in #["", "X", "ab", "•𝒜▼"] do
    let toCheck := substs i s
    for modified in toCheck do
      if let some d := levenshtein s modified s.length then
        if d > i.length then
          modify fun st => { st with failed := st.failed.push (s, modified, i.length, some d) }
        else
          modify fun st => { st with passed := st.passed + 1 }
      else
        modify fun st => { st with failed := st.failed.push (s, modified, i.length, none) }

/-- info: #["ayz", "xaz", "xya"] -/
#guard_msgs in
#eval substs "a" "xyz"

/-- info: #["byz", "abz", "ayb", "baz", "xbz", "xab", "bya", "xba", "xyb"] -/
#guard_msgs in
#eval substs "ab" "xyz"

/-- info: All 40494 tests passed -/
#guard_msgs in
#eval show IO Unit from do
  (strings.forM testSubsts *> report).run {} <&> (·.1)

/-!
# Testing Sequenced Operations

These tests check whether sequences of operations yield the expected results.
-/

inductive Spec where
  | ins (toInsert : String)
  | del (howMany : Nat)
  | subst (toSubst : String)

def Spec.maxDistance : Spec → Nat
  | .ins toInsert => toInsert.length
  | .del howMany => howMany
  | .subst toSubst => toSubst.length

def maxDistance (spec : List Spec) : Nat := spec.map (·.maxDistance) |>.sum

def Spec.apply : Spec → String → Array String
  | .ins toInsert, s => insertions toInsert s
  | .del howMany, s => deletions howMany s
  | .subst toSubst, s => substs toSubst s

def applySpec (spec : List Spec) (s : String) : Array String :=
  spec.foldl (init := #[s]) fun ss spec' =>
    ss.flatMap (spec'.apply)

def specs : List (List Spec) :=
  [[], [.ins "ab", .del 1], [.subst "a", .del 2]]

def testSpec (spec : List Spec) (s : String) : StateT Stats IO Unit := do
  for modified in applySpec spec s do
    let max := maxDistance spec
    if let some d := levenshtein s modified max then
      if d > max then
        modify fun st => { st with failed := st.failed.push (s, modified, max, some d) }
      else
        modify fun st => { st with passed := st.passed + 1 }
    else
      modify fun st => { st with failed := st.failed.push (s, modified, max, none) }

/-- info: All 2610 tests passed -/
#guard_msgs in
#eval show IO Unit from do
  Prod.fst <$> StateT.run (s := {})
    (((#["hello", "abcdefg", "abcdedcba", "𝒫(𝒜)"]).forM fun str =>
       specs.forM (testSpec · str)) *> report)

/-!
# Comparison Against Reference Implementation

This section compares against a slow-but-clear implementation with some chosen examples.
-/

/-- Naïve Levenshtein distance -/
def slow : (s1 s2 : List Char) → Nat
  | [], ys => ys.length
  | xs, [] => xs.length
  | (x :: xs), (y :: ys) =>
    if x = y then slow xs ys
    else 1 + min (min (slow xs (y :: ys)) (slow (x :: xs) ys)) (slow xs ys)

def tests := [
    ("kitten", "sitting"), ("Lean", "L∃∀N"), ("abc", "xyz"), ("", "ABC   "), ("hello", "quake"),
    ("", ""), ("aaaaaaa", "aaaaa"), ("aba", "aa"), ("aba", "ab"), ("abc", "ab"), ("abc", "zbc"),
    ("abcde", "abcdz"), ("abcde", "abXde")
  ]

def testPairs : StateT Stats IO Unit := do
  for (s1, s2) in tests do
    let expected := slow s1.toList s2.toList
    if let some d := levenshtein s1 s2 (s1.length + s2.length) then
      if d ≠ expected then
        modify fun st => { st with failed := st.failed.push (s1, s2, expected, some d) }
      else
        modify fun st => { st with passed := st.passed + 1 }
    else
      modify fun st => { st with failed := st.failed.push (s1, s2, expected, none) }

/-- info: All 13 tests passed -/
#guard_msgs in
#eval show IO Unit from do
  (testPairs *> report).run {} <&> Prod.fst
