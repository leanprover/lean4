-- set_option trace.Meta.FunInd true

import Lean

def test (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: l =>
    match x == 3 with
    | false => test l
    | true => test l


/--
info: test.induct_unfolding (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = false →
        motive l (test l) →
          motive (x :: l)
            (match x == 3 with
            | false => test l
            | true => test l))
  (case3 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = true →
        motive l (test l) →
          motive (x :: l)
            (match x == 3 with
            | false => test l
            | true => test l))
  (l : List Nat) : motive l (test l)
-/
#guard_msgs in
#check test.induct_unfolding

example (l : List Nat) : test l = sorry := by
  induction l using test.induct_unfolding with
  | case1 => sorry
  | case2 x l h ih =>
    simp [h]
    assumption
  | case3 x l h ih =>
    simp [h]
    assumption


opaque someFunction (x : Nat) (h : (x == 3) = false) : Nat
opaque someOtherFunction (x : Nat) (h : (x == 3) = true) : Nat

def deptest (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: l =>
    match h : x == 3 with
    | false => deptest l + someFunction x h
    | true => deptest l + someOtherFunction x h

/--
info: deptest.induct_unfolding (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = false →
        motive l (deptest l) →
          motive (x :: l)
            (match h : x == 3 with
            | false => deptest l + someFunction x h
            | true => deptest l + someOtherFunction x h))
  (case3 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = true →
        motive l (deptest l) →
          motive (x :: l)
            (match h : x == 3 with
            | false => deptest l + someFunction x h
            | true => deptest l + someOtherFunction x h))
  (l : List Nat) : motive l (deptest l)
-/
#guard_msgs in
#check deptest.induct_unfolding

example (l : List Nat) : deptest l = sorry := by
  induction l using deptest.induct_unfolding with
  | case1 => sorry
  | case2 x l h ih =>
    sorry
    -- simp [h] -- fails
    -- set_option trace.split.debug true in
    -- split
  | case3 x l h ih =>
    -- simp [h] -- fails
    sorry

theorem deptest.match_1.heq_1
  (motive : Bool → Sort v)
  (x : Bool)
  (h_1 : x = false → motive false)
  (h_2 : x = true → motive true)
  (h : x = false)
  : HEq (deptest.match_1 motive x h_1 h_2) (h_1 h) := by
  subst x
  apply heq_of_eq
  apply deptest.match_1.eq_1 motive h_1 h_2

theorem deptest.match_1.heq_2
  (motive : Bool → Sort v)
  (x : Bool)
  (h_1 : x = false → motive false)
  (h_2 : x = true → motive true)
  (h : x = true)
  : HEq (deptest.match_1 motive x h_1 h_2) (h_2 h) := by
  subst x
  apply heq_of_eq
  apply deptest.match_1.eq_2 motive h_1 h_2

theorem deptest.induct_unfolding_good
  (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 :
    ∀ (x : Nat) (l : List Nat),
      (h : (x == 3) = false) →
        motive l (deptest l) →
          motive (x :: l) (deptest l + someFunction x h))
  (case3 :
    ∀ (x : Nat) (l : List Nat),
      (h : (x == 3) = true) →
        motive l (deptest l) →
          motive (x :: l)
            (deptest l + someOtherFunction x h))
  (l : List Nat) : motive l (deptest l) := by
  unfold deptest
  split
  next => exact case1
  next _ x l =>
    refine deptest.match_1.splitter (motive := fun _ => motive (x :: l) _) (x == 3) (fun h => ?neg) (fun h => ?pos)
    case neg =>
      dsimp -- beta-redex the motive lambda
      have := deptest.match_1.heq_1 (motive := fun _ => Nat) _ (fun h => deptest l + someFunction x h) (fun h => deptest l + someOtherFunction x h) h
      refine (eq_of_heq this).substr (p := motive (x :: l)) ?_
      apply case2
      apply deptest.induct_unfolding_good motive case1 case2 case3
    next h =>
      dsimp -- beta-redex the motive lambda
      have := deptest.match_1.heq_2 (motive := fun _ => Nat) _ (fun h => deptest l + someFunction x h) (fun h => deptest l + someOtherFunction x h) h
      refine (eq_of_heq this).substr (p := motive (x :: l)) ?_
      apply case3
      apply deptest.induct_unfolding_good motive case1 case2 case3

def depTestOddType (l : List Nat) :
    match l with
    | [] => Unit
    | x :: _ =>
      if x == 3 then
        Unit
      else
        Nat
  :=
  match l with
  | [] => ()
  | x :: _ =>
    (match h : x == 3 with
    | false => someFunction x h
    | true => () : if x == 3 then Unit else Nat)

theorem depTestOddType.fun_cases_unfolding_good
  (motive :
    (l : List Nat) →
      (match l with
        | [] => Unit
        | x :: tail => if (x == 3) = true then Unit else Nat) →
        Prop)
  (case1 : motive [] ())
  (case2 :
    ∀ (x : Nat) (l : List Nat),
      (h : (x == 3) = false) →
        motive (x :: l)
          (if_neg (ne_true_of_eq_false h) ▸ someFunction x h : if (x == 3) = true then Unit else Nat))
  (case3 :
    ∀ (x : Nat) (l : List Nat),
      (h : (x == 3) = true) →
        motive (x :: l)
          (if_pos h ▸ () : if (x == 3) = true then Unit else Nat))
  (l : List Nat) : motive l (depTestOddType l) := sorry


open Lean Meta
def genGeneralizedMatchEqns (matchDeclName : Name) : MetaM Unit := do
  let matchEqns ← Match.getEquationsFor matchDeclName
  let some matcherInfo ← getMatcherInfo? matchDeclName | throwError "expected match info for {matchDeclName}"
  let matcherVal ← getConstVal matchDeclName
  for eqnName in matchEqns.eqnNames do
    let eqnVal ← getConstVal eqnName
    unless matcherVal.levelParams = eqnVal.levelParams do
      throwError "level params of {eqnName} do not match the level params of {matchDeclName}"
    forallTelescope matcherVal.type fun xs _ => do
      assert! matcherInfo.numParams + 1 + matcherInfo.numDiscrs + matcherInfo.numAlts == xs.size
      -- let params := xs[0:matcherInfo.numParams]
      -- let motive := xs[matcherInfo.numParams]!
      let discrs := xs[matcherInfo.getFirstDiscrPos:matcherInfo.getFirstAltPos]
      let alts := xs[matcherInfo.getFirstAltPos:]
      let lhs := mkAppN (← mkConstWithLevelParams matchDeclName) xs

      let eqnType := eqnVal.type
      let eqnType ← instantiateForall eqnType xs[:matcherInfo.numParams + 1]
      let (hs, _, eqType) ← forallMetaTelescope eqnType
      let some (_, eqLhs, eqRhs) := eqType.eq?
        | throwError "expected equation type for {eqnName}"
      unless eqLhs.isAppOfArity matchDeclName xs.size do
        throwError "unexpected arity of {matchDeclName} in{indentExpr eqLhs}"
      let mut eqHyps := #[]
      for d1 in discrs, d2 in eqLhs.getAppArgs[matcherInfo.getFirstDiscrPos:] do
        eqHyps := eqHyps.push (← mkEqHEq d1 d2)
      for a1 in alts, a2 in eqLhs.getAppArgs[matcherInfo.getFirstAltPos:] do
        a2.mvarId!.assign a1
      let hs ← hs.filterM fun h => do return ! (← h.mvarId!.isAssigned)

      let genEqType ← mkForallFVars (xs ++ hs) (← mkHEq lhs eqRhs)
      logInfo m!"{eqnName} : {genEqType}"
      check genEqType
      pure ()



def myTest {α}
  (mmotive : (x : List α) → Sort v)
  (x : List α)
  (h_1 : (a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc))
  (h_2 : (x' : List α) → x = x' → mmotive x') : mmotive x :=
  match (generalizing := false) h : x with
  | a :: dc => h_1 a dc h
  | x' => h_2 x' h

run_meta do
  genGeneralizedMatchEqns ``myTest.match_1

-- #check myTest.match_1
-- #check myTest.match_1.eq_2
