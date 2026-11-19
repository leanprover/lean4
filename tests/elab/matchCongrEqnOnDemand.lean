import Lean
/-!
Each congruence equation `f.match_1.congr_eq_i` is generated on demand, independently of the other
ones. A match equation that is not proved by `rfl` only needs the congruence equation of its
alternative. So, for a `match` on literals with a catch-all, generating the match equations
generates only the congruence equation of the catch-all.
-/
open Lean Meta

def natLits : Nat → Nat
  | 0 => 0
  | 5 => 1
  | 10 => 2
  | _ => 3

/-- Returns the indices `i` such that `matcherName.congr_eq_i` is in the environment. -/
def congrEqnsInEnv (matcherName : Name) : MetaM (List Nat) := do
  let some info ← getMatcherInfo? matcherName | throwError "matcher expected: {matcherName}"
  let env ← getEnv
  return (List.range info.numAlts).map (· + 1) |>.filter fun i =>
    env.contains ((matcherName.str "congr_eq").appendIndexAfter i)

/-- info: [] -/
#guard_msgs in
run_meta do logInfo m!"{← congrEqnsInEnv ``natLits.match_1}"

/-! The match equations of the literals are proved by `rfl`. Only the catch-all needs `congr_eq_4`. -/

/-- info: [4] -/
#guard_msgs in
run_meta do
  discard <| Match.getEquationsFor ``natLits.match_1
  logInfo m!"{← congrEqnsInEnv ``natLits.match_1}"

/-! Referring to a congruence equation by name generates only that equation. -/

/-- info: [2, 4] -/
#guard_msgs in
run_meta do
  discard <| realizeGlobalConstNoOverload (mkIdent `natLits.match_1.congr_eq_2)
  logInfo m!"{← congrEqnsInEnv ``natLits.match_1}"

/-- error: Unknown identifier `natLits.match_1.congr_eq_5` -/
#guard_msgs in
example := @natLits.match_1.congr_eq_5

/-- error: Unknown identifier `natLits.match_1.congr_eq_0` -/
#guard_msgs in
example := @natLits.match_1.congr_eq_0

/-! `Match.genMatchCongrEqns` generates the remaining ones. -/

/--
info: [natLits.match_1.congr_eq_1, natLits.match_1.congr_eq_2, natLits.match_1.congr_eq_3, natLits.match_1.congr_eq_4]
---
info: [1, 2, 3, 4]
-/
#guard_msgs in
run_meta do
  logInfo m!"{← Match.genMatchCongrEqns ``natLits.match_1}"
  logInfo m!"{← congrEqnsInEnv ``natLits.match_1}"

/-! A single congruence equation of an alternative with overlaps. -/

def overlap : Option Nat → Nat
  | some 0 => 1
  | some n => n
  | _ => 3

/--
info: overlap.match_1.congr_eq_3.{u_1} (motive : Option Nat → Sort u_1) (x✝ : Option Nat) (h_1 : Unit → motive (some 0))
  (h_2 : (n : Nat) → motive (some n)) (h_3 : (x : Option Nat) → motive x) (x✝¹ : Option Nat) (heq_1 : x✝ = x✝¹) :
  (x✝¹ = some 0 → False) →
    (∀ (n : Nat), x✝¹ = some n → False) →
      (match x✝ with
        | some 0 => h_1 ()
        | some n => h_2 n
        | x => h_3 x) ≍
        h_3 x✝¹
-/
#guard_msgs in
#check overlap.match_1.congr_eq_3

/-- info: [3] -/
#guard_msgs in
run_meta do
  discard <| realizeGlobalConstNoOverload (mkIdent `overlap.match_1.congr_eq_3)
  logInfo m!"{← congrEqnsInEnv ``overlap.match_1}"
