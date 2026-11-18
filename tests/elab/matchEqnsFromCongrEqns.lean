import Lean
/-!
A match equation that is not proved by `rfl` is proved as an instance of the corresponding
congruence equation: `eq_of_heq (congr_eq_i ..)`. The proof is not repeated in both theorems.
-/
open Lean Meta

def strLits : String → Nat
  | "a" => 1
  | "b" => 2
  | _ => 3

def overlap : Option Nat → Nat
  | some 0 => 1
  | some n => n
  | _ => 3

inductive V : Nat → Type
  | nil : V 0
  | cons : Nat → V n → V (n+1)

def indexed : (n : Nat) → V n → Nat
  | _, .nil => 0
  | _, .cons a _ => a

def discrEq (x : Option Nat) : Nat :=
  match _h : x with
  | some 0 => 1
  | some n => n
  | none => 3

def twoDiscrs : Nat → Option String → Nat
  | 0, some "a" => 1
  | n+1, none => n
  | _, _ => 3

def ctors : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: _ => x + y

def pair (p : Nat × Nat) : Nat :=
  match p with
  | (0, b) => b
  | (a, _) => a

def named : List Nat → List Nat
  | [] => []
  | [0] => [1]
  | xs@(_ :: ys) => xs ++ ys

/--
Checks that each match equation of `matcherName` is proved by `Eq.refl` or as an instance of its
congruence equation, and returns the number of equations of each kind.
-/
def checkMatchEqns (matcherName : Name) : MetaM (Nat × Nat) := do
  let eqns ← Match.getEquationsFor matcherName
  let congrEqns ← Match.genMatchCongrEqns matcherName
  let mut numRfl := 0
  let mut numCongr := 0
  for eqn in eqns.eqnNames, congrEqn in congrEqns do
    let some (.thmInfo info) := (← getEnv).find? eqn | throwError "theorem expected: {eqn}"
    let proof := info.value.getLambdaBody
    if proof.isAppOf ``Eq.refl then
      numRfl := numRfl + 1
    else if proof.isAppOfArity ``eq_of_heq 4 && proof.appArg!.isAppOf congrEqn then
      numCongr := numCongr + 1
    else
      throwError "unexpected proof for {privateToUserName eqn}{indentExpr info.value}"
  return (numRfl, numCongr)

/-- info: (0, 3) -/
#guard_msgs in
run_meta do logInfo m!"{← checkMatchEqns ``strLits.match_1}"

/-- info: (1, 2) -/
#guard_msgs in
run_meta do logInfo m!"{← checkMatchEqns ``overlap.match_1}"

/-- info: (2, 0) -/
#guard_msgs in
run_meta do logInfo m!"{← checkMatchEqns ``indexed.match_1}"

/-- info: (2, 1) -/
#guard_msgs in
run_meta do logInfo m!"{← checkMatchEqns ``discrEq.match_1}"

/-- info: (1, 2) -/
#guard_msgs in
run_meta do logInfo m!"{← checkMatchEqns ``twoDiscrs.match_1}"

/-- info: (3, 0) -/
#guard_msgs in
run_meta do logInfo m!"{← checkMatchEqns ``ctors.match_1}"

/-- info: (1, 1) -/
#guard_msgs in
run_meta do logInfo m!"{← checkMatchEqns ``pair.match_1}"

run_meta do discard <| checkMatchEqns ``named.match_1

/-! The equations are still usable. -/

example : strLits "b" = 2 := by simp [strLits]
example (_ : s ≠ "a") (_ : s ≠ "b") : strLits s = 3 := by simp [strLits]
example (_ : n ≠ 0) : overlap (some n) = n := by simp [overlap]
example : overlap none = 3 := by simp [overlap]
example : twoDiscrs 0 (some "a") = 1 := by simp [twoDiscrs]
example : twoDiscrs (n+1) none = n := by simp [twoDiscrs]
example : pair (3, 4) = 3 := by simp [pair]
example : named [0] = [1] := by simp [named]
example : named [2, 3] = [2, 3, 3] := by simp [named]
example (x : Option Nat) : discrEq x = overlap x := by
  unfold discrEq overlap
  split <;> split <;> simp_all

/-!
A congruence equation is proved by reflexivity when its match equation is. Otherwise, a `match`
with many literal alternatives whose equations are proved by reflexivity would get large
congruence equation proofs as soon as one of its equations, here the last one, needs them.
-/

def finLits : Fin 1024 → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

/-- info: (3, 1) -/
#guard_msgs in
run_meta do logInfo m!"{← checkMatchEqns ``finLits.match_1}"

run_meta do
  let congrEqns ← Match.genMatchCongrEqns ``finLits.match_1
  for congrEqn in congrEqns[*...3] do
    let some (.thmInfo info) := (← getEnv).find? congrEqn | throwError "theorem expected: {congrEqn}"
    unless (info.value.find? (·.isConstOf ``HEq.refl)).isSome do
      throwError "unexpected proof for {congrEqn}{indentExpr info.value}"
