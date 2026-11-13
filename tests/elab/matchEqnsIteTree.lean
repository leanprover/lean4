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
