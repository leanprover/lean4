import Lean
/-!
Generating the equations of matchers whose compiled form is a tree of `dite (x = value) ..` nodes,
possibly interleaved with `casesOn`. The catch-all equations are proved by splitting the tree and
refuting each `isTrue` branch with an overlap hypothesis.
-/
open Lean Meta Elab Command

/-- Generates the equations and the congruence equations of the given matcher. -/
elab "#gen_match_eqns " id:ident : command => liftTermElabM do
  let declName ← realizeGlobalConstNoOverloadCore id.getId
  discard <| Match.getEquationsFor declName
  discard <| Match.genMatchCongrEqns declName

def nested : Option String → Nat
  | some "a0" => 0
  | some "a1" => 1
  | some "a2" => 2
  | some "a3" => 3
  | _ => 1000
#gen_match_eqns nested.match_1

def twoDiscrs : String → Nat → Nat
  | "a", 0 => 1
  | "b", _ => 2
  | "c", 1 => 3
  | "d", _ => 4
  | "e", 2 => 5
  | "a", 1 => 11
  | "c", 2 => 12
  | _,   _ => 6
#gen_match_eqns twoDiscrs.match_1

def underCtors : Option (String × Nat) → Nat
  | some ("a", 0) => 1
  | some ("b", _) => 2
  | none => 3
  | some ("a", 1) => 4
  | _ => 5
#gen_match_eqns underCtors.match_1

def inList : List String → Nat
  | ["a"] => 1
  | ["a", "b"] => 2
  | "c" :: _ => 3
  | _ :: "d" :: _ => 4
  | _ => 5
#gen_match_eqns inList.match_1

def twoStrings : String → String → Nat
  | "a", "b" => 1
  | "a", _ => 2
  | _, "b" => 3
  | "c", "d" => 4
  | _, _ => 5
#gen_match_eqns twoStrings.match_1

def withOffset : String → Nat → Nat
  | "a", n+2 => n
  | "b", 0 => 1
  | "a", 1 => 2
  | _, 5 => 3
  | _, _ => 4
#gen_match_eqns withOffset.match_1

def otherLits : Char → Fin 5 → UInt8 → Int → Nat
  | 'a', 3, _, _ => 1
  | _, _, 7, -1 => 2
  | 'b', _, 7, 2 => 3
  | _, 0, _, _ => 4
  | _, _, _, _ => 5
#gen_match_eqns otherLits.match_1

def inPair : (Option String × List Nat) → Nat
  | (some "a", [1]) => 1
  | (some "a", _) => 2
  | (_, [2]) => 3
  | (some "b", [3, 4]) => 4
  | (none, _) => 5
  | _ => 6
#gen_match_eqns inPair.match_1

def mixed : String → Bool → Option Nat → Nat
  | "a", true, some 0 => 1
  | "a", false, _ => 2
  | "b", _, some (n+1) => n
  | s, true, none => s.length
  | _, _, _ => 5
#gen_match_eqns mixed.match_1

/-! A later discriminant depends on a variable matched against literals. -/
def dependent : (n : Nat) → Fin (n+1) → String → Nat
  | 0, _, "a" => 1
  | 1, i, "b" => i
  | 2, _, "a" => 2
  | 1, _, _ => 3
  | _, _, _ => 4
#gen_match_eqns dependent.match_1

/-!
The catch-all equations of the following matchers reach a `casesOn` application after one, two,
and three tests `x = value` have succeeded. The equalities for these tests are substituted before
the `casesOn` application is processed.
-/
def oneTest : List String → Nat
  | ["a"] => 1
  | ["b"] => 2
  | _ => 3
#gen_match_eqns oneTest.match_1

def twoTests : String → String → List Nat → Nat
  | "a", "b", [] => 1
  | "a", "c", [1] => 2
  | "d", "b", _ :: _ => 3
  | _, _, _ => 4
#gen_match_eqns twoTests.match_1

def threeTests : String → Nat → Char → Option Bool → Nat
  | "a", 0, 'x', none => 1
  | "a", 0, 'y', some true => 2
  | "a", 1, 'x', some _ => 3
  | _, _, _, _ => 4
#gen_match_eqns threeTests.match_1

/-!
The matcher tests the `Nat` before the `Char` after `x = "a"` succeeds, and the `Char` before the
`Nat` after `x = "b"` succeeds.
-/
def testOrder : String → Nat → Char → Nat
  | "a", 1, 'a' => 1
  | "b", _, 'b' => 2
  | "b", 2, 'c' => 3
  | _, _, _ => 4
#gen_match_eqns testOrder.match_1

/-!
The patterns `5` and `5.0` denote the same `Float` value. The matcher tests `x = 5` once, and the
overlap hypothesis for the second alternative is `x = 5.0 → s = "b" → False`.
-/
def floatValues : Float → String → Nat
  | 5, "a" => 1
  | 5.0, "b" => 2
  | _, _ => 3
#gen_match_eqns floatValues.match_1
