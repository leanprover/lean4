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

partial def forallAltTelescope (altType : Expr) (altNumParams numDiscrEqs : Nat)
    (k : (ys : Array Expr) → (eqs : Array Expr) → (args : Array Expr) → (mask : Array Bool) → (type : Expr) → MetaM α)
    : MetaM α := do
  go #[] #[] #[] #[] 0 altType
where
  go (ys : Array Expr) (eqs : Array Expr) (args : Array Expr) (mask : Array Bool) (i : Nat) (type : Expr) : MetaM α := do
    let type ← whnfForall type
    if i < altNumParams then
      let Expr.forallE n d b .. := type
        | throwError "expecting {altNumParams} parameters, including {numDiscrEqs} equalities, but found type{indentExpr altType}"
      if i < altNumParams - numDiscrEqs then
        let d ← Match.unfoldNamedPattern d
        withLocalDeclD n d fun y => do
          let typeNew := b.instantiate1 y
          -- if let some (_, lhs, rhs) ← matchEq? d then
          --   if lhs.isFVar && ys.contains lhs && args.contains lhs && isNamedPatternProof typeNew y then
          --      let some j  := ys.finIdxOf? lhs | unreachable!
          --      let ys      := ys.eraseIdx j
          --      let some k  := args.idxOf? lhs | unreachable!
          --      let mask    := mask.set! k false
          --      let args    := args.map fun arg => if arg == lhs then rhs else arg
          --      let arg     ← mkEqRefl rhs
          --      let typeNew := typeNew.replaceFVar lhs rhs
          --      return ← withReplaceFVarId lhs.fvarId! rhs do
          --       withReplaceFVarId y.fvarId! arg do
          --         go ys eqs (args.push arg) (mask.push false) (i+1) typeNew
          go (ys.push y) eqs (args.push y) (mask.push true) (i+1) typeNew
      else
        -- let arg ← if let some (_, _, rhs) ← matchEq? d then
        --   mkEqRefl rhs
        -- else if let some (_, _, _, rhs) ← matchHEq? d then
        --   mkHEqRefl rhs
        -- else
        --   throwError "unexpected match alternative type{indentExpr altType}"
        withLocalDeclD n d fun eq => do
          let typeNew := b.instantiate1 eq
          go ys (eqs.push eq) (args.push eq) (mask.push false) (i+1) typeNew
    else
      let type ← Match.unfoldNamedPattern type
      /- Recall that alternatives that do not have variables have a `Unit` parameter to ensure
         they are not eagerly evaluated. -/
      if ys.size == 1 then
        if (← inferType ys[0]!).isConstOf ``Unit && !(← dependsOn type ys[0]!.fvarId!) then
          let rhs := mkConst ``Unit.unit
          return ← withReplaceFVarId ys[0]!.fvarId! rhs do
          return (← k #[] #[] #[rhs] #[false] type)
      k ys eqs args mask type

  isNamedPatternProof (type : Expr) (h : Expr) : Bool :=
    Option.isSome <| type.find? fun e =>
      if let some e := Match.isNamedPattern? e then
        e.appArg! == h
      else
        false

def genGeneralizedMatchEqns (matchDeclName : Name) : MetaM Unit := do
  let baseName := mkPrivateName (← getEnv) matchDeclName
  withConfig (fun c => { c with etaStruct := .none }) do
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "'{matchDeclName}' is not a matcher function"
  let numDiscrEqs := Match.getNumEqsFromDiscrInfos matchInfo.discrInfos
  forallTelescopeReducing constInfo.type fun xs matchResultType => do
    let mut eqnNames := #[]
    let params := xs[:matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]!
    let alts   := xs[xs.size - matchInfo.numAlts:]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx : firstDiscrIdx + matchInfo.numDiscrs]
    let mut notAlts := #[]
    let mut idx := 1
    let mut splitterAltTypes := #[]
    let mut splitterAltNumParams := #[]
    let mut altArgMasks := #[] -- masks produced by `forallAltTelescope`
    for i in [:alts.size] do
      let altNumParams := matchInfo.altNumParams[i]!
      let thmName := baseName ++ ((`gen_eq).appendIndexAfter idx)
      eqnNames := eqnNames.push thmName
      let (notAlt, splitterAltType, splitterAltNumParam, argMask) ←
          forallAltTelescope (← inferType alts[i]!) altNumParams numDiscrEqs
          fun ys eqs rhsArgs argMask altResultType => do
        let patterns := altResultType.getAppArgs
        let mut hs := #[]
        for notAlt in notAlts do
          let h ← instantiateForall notAlt patterns
          if let some h ← Match.simpH? h patterns.size then
            hs := hs.push h
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let splitterAltType ← mkForallFVars ys (← hs.foldrM (init := (← mkForallFVars eqs altResultType)) (mkArrow · ·))
        let splitterAltNumParam := hs.size + ys.size
        -- Create a proposition for representing terms that do not match `patterns`
        let mut notAlt := mkConst ``False
        for discr in discrs.toArray.reverse, pattern in patterns.reverse do
          notAlt ← mkArrow (← mkEqHEq discr pattern) notAlt
        notAlt ← mkForallFVars (discrs ++ ys) notAlt
        /- Recall that when we use the `h : discr`, the alternative type depends on the discriminant.
           Thus, we need to create new `alts`. -/
        id do
        -- Match.withNewAlts numDiscrEqs discrs patterns alts fun alts => do
          let alt := alts[i]!
          let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ discrs ++ alts)
          let rhs := mkAppN alt rhsArgs
          let thmType ← mkHEq lhs rhs
          let thmType ← hs.foldrM (init := thmType) (mkArrow · ·)
          -- let thmVal ← mkFreshExprSyntheticOpaqueMVar thmType
          let thmType ← mkForallFVars (params ++ #[motive] ++ discrs ++ alts ++ ys ++ eqs) thmType
          let thmType ← Match.unfoldNamedPattern thmType
          let thmVal ← Match.proveCondEqThm matchDeclName thmType
          addDecl <| Declaration.thmDecl {
            name        := thmName
            levelParams := constInfo.levelParams
            type        := thmType
            value       := thmVal
          }
          return (notAlt, splitterAltType, splitterAltNumParam, argMask)
      notAlts := notAlts.push notAlt
      splitterAltTypes := splitterAltTypes.push splitterAltType
      splitterAltNumParams := splitterAltNumParams.push splitterAltNumParam
      altArgMasks := altArgMasks.push argMask
      trace[Meta.Match.matchEqs] "splitterAltType: {splitterAltType}"
      idx := idx + 1


def myTest {α}
  (mmotive : (x : List α) → Sort v)
  (x : List α)
  (h_1 : (a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc))
  (h_2 : (x' : List α) → x = x' → mmotive x') : mmotive x :=
  match (generalizing := false) h : x with
  | a :: dc => h_1 a dc h
  | x' => h_2 x' h

-- set_option trace.Meta.Match.matchEqs true in
run_meta do
  genGeneralizedMatchEqns ``myTest.match_1

-- #check myTest.match_1
/--
info: myTest.match_1.splitter.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc))
  (h_2 : (x' : List α) → (∀ (a : α) (dc : List α), x' = a :: dc → False) → x✝ = x' → motive x') : motive x✝
-/
#guard_msgs in
#check myTest.match_1.splitter
/--
info: myTest.match_1.gen_eq_1.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc)) (h_2 : (x' : List α) → x✝ = x' → motive x') (a : α)
  (dc : List α) (h : x✝ = a :: dc) :
  HEq
    (match h : x✝ with
    | a :: dc => h_1 a dc h
    | x' => h_2 x' h)
    (h_1 a dc h)
-/
#guard_msgs in
#check myTest.match_1.gen_eq_1

/--
info: myTest.match_1.gen_eq_2.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α)
  (h_1 : (a : α) → (dc : List α) → x✝ = a :: dc → motive (a :: dc)) (h_2 : (x' : List α) → x✝ = x' → motive x')
  (x' : List α) (h : x✝ = x') :
  (∀ (a : α) (dc : List α), x' = a :: dc → False) →
    HEq
      (match h : x✝ with
      | a :: dc => h_1 a dc h
      | x' => h_2 x' h)
      (h_2 x' h)
-/
#guard_msgs in
#check myTest.match_1.gen_eq_2
