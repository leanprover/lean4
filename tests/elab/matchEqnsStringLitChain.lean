import Lean
/-!
A matcher that starts with a chain of at least 32 tests on `String` literals has an auxiliary
theorem `strLitChain` with one case for each test, proved with a single traversal of the chain.
The congruence equations of the alternatives of the chain, and of the alternative that follows it,
are cases of this theorem (#16313).
-/
open Lean Meta

/-- Returns the statement of the theorem `strLitChain` of `matcherName`, if it has one. -/
def strLitChain? (matcherName : Name) : MetaM (Option Expr) := do
  discard <| Match.genMatchCongrEqns matcherName
  let name := mkPrivateName (← getEnv) matcherName ++ `strLitChain
  let some (.thmInfo info) := (← getEnv).find? name | return none
  return some info.type

/-- Returns, for each congruence equation of `matcherName`, whether it is proved using `strLitChain`. -/
def chainEqns (matcherName : Name) : MetaM (Array Bool) := do
  let name := mkPrivateName (← getEnv) matcherName ++ `strLitChain
  (← Match.genMatchCongrEqns matcherName).mapM fun eqn => do
    let some (.thmInfo info) := (← getEnv).find? eqn | throwError "theorem expected: {eqn}"
    return (info.value.find? (·.isConstOf name)).isSome

/-! A matcher with less than 32 literals does not have the theorem. -/

def small : String → Nat
  | "a" => 0
  | "b" => 1
  | "c" => 2
  | _ => 3

/-- info: (none, [false, false, false, false]) -/
#guard_msgs in
run_meta do logInfo m!"{((← strLitChain? ``small.match_1).map fun _ => (), ← chainEqns ``small.match_1)}"

/-! A matcher with 32 literals. -/

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
Checks that `type` is `∀ motive x alts (r : motive x), r = matcher motive x alts → cases`, where
`cases` is `(x = "lit_0" → r ≍ alt₀ ()) ∧ (¬ x = "lit_0" → (x = "lit_1" → r ≍ alt₁ ()) ∧ ..)`,
and returns the number of tests.
-/
partial def numCases (type : Expr) : MetaM Nat :=
  forallTelescope type fun xs cases => go xs cases 0
where
  go (xs : Array Expr) (cases : Expr) (i : Nat) : MetaM Nat := do
    let x := xs[1]!
    let r := xs[xs.size - 2]!
    match_expr cases with
    | And pos neg =>
      let .forallE _ c heq _ := pos | throwError "unexpected case{indentExpr pos}"
      let .forallE _ nc rest _ := neg | throwError "unexpected case{indentExpr neg}"
      let some (_, lhs, _, rhs) := heq.heq? | throwError "unexpected case{indentExpr pos}"
      unless c == (← mkEq x (mkStrLit s!"lit_{i}")) && nc == mkNot c && lhs == r && rhs == mkApp xs[i+2]! (mkConst ``Unit.unit) do
        throwError "unexpected case{indentExpr cases}"
      go xs rest (i+1)
    | _ =>
      let some (_, lhs, _, rhs) := cases.heq? | throwError "unexpected case{indentExpr cases}"
      unless lhs == r && rhs == mkApp xs[i+2]! x do throwError "unexpected case{indentExpr cases}"
      return i

/-- info: 32 -/
#guard_msgs in
run_meta do
  let some type ← strLitChain? ``f.match_1 | throwError "theorem expected"
  logInfo m!"{← numCases type}"

run_meta do
  unless (← chainEqns ``f.match_1).all id do throwError "unexpected proof"

example : f "lit_0" = 0 := by simp [f]
example : f "lit_17" = 17 := by simp [f]
example : f "lit_31" = 31 := by simp [f]
example : f "lit_32" = 32 := by simp [f]

/-! A chain followed by an alternative that is not a catch-all, and a polymorphic function. -/

def thenVar : String → Nat
  | "lit_0" => 0 | "lit_1" => 1 | "lit_2" => 2 | "lit_3" => 3
  | "lit_4" => 4 | "lit_5" => 5 | "lit_6" => 6 | "lit_7" => 7
  | "lit_8" => 8 | "lit_9" => 9 | "lit_10" => 10 | "lit_11" => 11
  | "lit_12" => 12 | "lit_13" => 13 | "lit_14" => 14 | "lit_15" => 15
  | "lit_16" => 16 | "lit_17" => 17 | "lit_18" => 18 | "lit_19" => 19
  | "lit_20" => 20 | "lit_21" => 21 | "lit_22" => 22 | "lit_23" => 23
  | "lit_24" => 24 | "lit_25" => 25 | "lit_26" => 26 | "lit_27" => 27
  | "lit_28" => 28 | "lit_29" => 29 | "lit_30" => 30 | "lit_31" => 31
  | s => s.length

example : thenVar "lit_5" = 5 := by simp [thenVar]

def poly {α : Type u} (a b : α) : String → α
  | "lit_0" => a | "lit_1" => a | "lit_2" => a | "lit_3" => a
  | "lit_4" => a | "lit_5" => a | "lit_6" => a | "lit_7" => a
  | "lit_8" => a | "lit_9" => a | "lit_10" => a | "lit_11" => a
  | "lit_12" => a | "lit_13" => a | "lit_14" => a | "lit_15" => a
  | "lit_16" => a | "lit_17" => a | "lit_18" => a | "lit_19" => a
  | "lit_20" => a | "lit_21" => a | "lit_22" => a | "lit_23" => a
  | "lit_24" => a | "lit_25" => a | "lit_26" => a | "lit_27" => a
  | "lit_28" => a | "lit_29" => a | "lit_30" => a | "lit_31" => a
  | _ => b

example : poly 1 2 "lit_7" = 1 := by simp [poly]
example : poly 1 2 "x" = 2 := by simp [poly]

/-!
Matchers with at least 32 literals that do not start with a chain of tests on a single `String`
discriminant. Their equations are still generated.
-/

def twoDiscrs : String → Bool → Nat
  | "lit_0", _ => 0 | "lit_1", _ => 1 | "lit_2", _ => 2 | "lit_3", _ => 3
  | "lit_4", _ => 4 | "lit_5", _ => 5 | "lit_6", _ => 6 | "lit_7", _ => 7
  | "lit_8", _ => 8 | "lit_9", _ => 9 | "lit_10", _ => 10 | "lit_11", _ => 11
  | "lit_12", _ => 12 | "lit_13", _ => 13 | "lit_14", _ => 14 | "lit_15", _ => 15
  | "lit_16", _ => 16 | "lit_17", _ => 17 | "lit_18", _ => 18 | "lit_19", _ => 19
  | "lit_20", _ => 20 | "lit_21", _ => 21 | "lit_22", _ => 22 | "lit_23", _ => 23
  | "lit_24", _ => 24 | "lit_25", _ => 25 | "lit_26", _ => 26 | "lit_27", _ => 27
  | "lit_28", _ => 28 | "lit_29", _ => 29 | "lit_30", _ => 30 | "lit_31", _ => 31
  | _, _ => 32

def nested : Option String → Nat
  | some "lit_0" => 0 | some "lit_1" => 1 | some "lit_2" => 2 | some "lit_3" => 3
  | some "lit_4" => 4 | some "lit_5" => 5 | some "lit_6" => 6 | some "lit_7" => 7
  | some "lit_8" => 8 | some "lit_9" => 9 | some "lit_10" => 10 | some "lit_11" => 11
  | some "lit_12" => 12 | some "lit_13" => 13 | some "lit_14" => 14 | some "lit_15" => 15
  | some "lit_16" => 16 | some "lit_17" => 17 | some "lit_18" => 18 | some "lit_19" => 19
  | some "lit_20" => 20 | some "lit_21" => 21 | some "lit_22" => 22 | some "lit_23" => 23
  | some "lit_24" => 24 | some "lit_25" => 25 | some "lit_26" => 26 | some "lit_27" => 27
  | some "lit_28" => 28 | some "lit_29" => 29 | some "lit_30" => 30 | some "lit_31" => 31
  | _ => 32

def withEq (s : String) : Nat :=
  match _h : s with
  | "lit_0" => 0 | "lit_1" => 1 | "lit_2" => 2 | "lit_3" => 3
  | "lit_4" => 4 | "lit_5" => 5 | "lit_6" => 6 | "lit_7" => 7
  | "lit_8" => 8 | "lit_9" => 9 | "lit_10" => 10 | "lit_11" => 11
  | "lit_12" => 12 | "lit_13" => 13 | "lit_14" => 14 | "lit_15" => 15
  | "lit_16" => 16 | "lit_17" => 17 | "lit_18" => 18 | "lit_19" => 19
  | "lit_20" => 20 | "lit_21" => 21 | "lit_22" => 22 | "lit_23" => 23
  | "lit_24" => 24 | "lit_25" => 25 | "lit_26" => 26 | "lit_27" => 27
  | "lit_28" => 28 | "lit_29" => 29 | "lit_30" => 30 | "lit_31" => 31
  | _ => 32

/-- info: [false, false, false] -/
#guard_msgs in
run_meta do
  logInfo m!"{[(← chainEqns ``twoDiscrs.match_1).any id, (← chainEqns ``nested.match_1).any id, (← chainEqns ``withEq.match_1).any id]}"

example : twoDiscrs "lit_3" true = 3 := by simp [twoDiscrs]
example : nested (some "lit_3") = 3 := by simp [nested]
example : withEq "lit_3" = 3 := by simp [withEq]

/-!
The size of the proof of the congruence equation of a literal does not depend on the number of
tests that follow it: `f` and `long` start with the same 32 literals.
-/

def long : String → Nat
  | "lit_0" => 0 | "lit_1" => 1 | "lit_2" => 2 | "lit_3" => 3
  | "lit_4" => 4 | "lit_5" => 5 | "lit_6" => 6 | "lit_7" => 7
  | "lit_8" => 8 | "lit_9" => 9 | "lit_10" => 10 | "lit_11" => 11
  | "lit_12" => 12 | "lit_13" => 13 | "lit_14" => 14 | "lit_15" => 15
  | "lit_16" => 16 | "lit_17" => 17 | "lit_18" => 18 | "lit_19" => 19
  | "lit_20" => 20 | "lit_21" => 21 | "lit_22" => 22 | "lit_23" => 23
  | "lit_24" => 24 | "lit_25" => 25 | "lit_26" => 26 | "lit_27" => 27
  | "lit_28" => 28 | "lit_29" => 29 | "lit_30" => 30 | "lit_31" => 31
  | "lit_32" => 32 | "lit_33" => 33 | "lit_34" => 34 | "lit_35" => 35
  | "lit_36" => 36 | "lit_37" => 37 | "lit_38" => 38 | "lit_39" => 39
  | "lit_40" => 40 | "lit_41" => 41 | "lit_42" => 42 | "lit_43" => 43
  | "lit_44" => 44 | "lit_45" => 45 | "lit_46" => 46 | "lit_47" => 47
  | _ => 48

run_meta do
  let shortEqns ← Match.genMatchCongrEqns ``f.match_1
  let longEqns ← Match.genMatchCongrEqns ``long.match_1
  let size (declName : Name) : MetaM Nat := do
    let some (.thmInfo info) := (← getEnv).find? declName | throwError "theorem expected: {declName}"
    (ShareCommon.shareCommon info.value).numObjs
  for i in [0:30] do
    let d₁ := (← size shortEqns[i+1]!) - (← size shortEqns[i]!)
    let d₂ := (← size longEqns[i+1]!) - (← size longEqns[i]!)
    unless d₁ == d₂ do
      throwError "proof size depends on the number of remaining tests: {d₁} {d₂}"
