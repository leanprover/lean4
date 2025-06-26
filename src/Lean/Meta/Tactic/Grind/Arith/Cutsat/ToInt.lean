/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.ToIntLemmas
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat

private def reportMissingToIntAdapter (type : Expr) (instType : Expr) : MetaM Unit := do
  trace[grind.debug.cutsat.debug] "`ToInt` initialization failure, failed to synthesize{indentExpr instType}\nfor type{indentExpr type}"

private def throwMissingDecl (declName : Name) : MetaM Unit :=
  throwError "`grind cutsat`, unexpected missing declaration {declName}"

private def checkDecl (declName : Name) : MetaM Unit := do
  unless (← getEnv).contains declName do
    throwMissingDecl declName

private def mkOpCongr (type : Expr) (u : Level) (toIntInst : Expr) (rangeExpr : Expr) (range : Grind.IntInterval) (opBaseName : Name) (thmName : Name) : MetaM ToIntCongr := do
  let op := mkApp (mkConst opBaseName [u]) type
  let .some opInst ← trySynthInstance op | return {}
  let toIntOpName := ``Grind.ToInt ++ opBaseName
  checkDecl toIntOpName
  let toIntOp := mkApp4 (mkConst toIntOpName [u]) type opInst rangeExpr toIntInst
  let .some toIntOpInst ← trySynthInstance toIntOp
    | reportMissingToIntAdapter type toIntOp; return {}
  checkDecl thmName
  let c := mkApp5 (mkConst thmName [u]) type rangeExpr toIntInst opInst toIntOpInst
  let env ← getEnv
  let cwwName := thmName ++ `ww
  let cwlName := thmName ++ `wl
  let cwrName := thmName ++ `wr
  let c_ww? := if range.isFinite && env.contains cwwName then
    some <| mkApp6 (mkConst cwwName [u]) type rangeExpr toIntInst opInst toIntOpInst reflBoolTrue
  else
    none
  let c_wl? := if range.isFinite && range.nonEmpty && env.contains cwwName then
    some <| mkApp7 (mkConst cwlName [u]) type rangeExpr toIntInst opInst toIntOpInst reflBoolTrue reflBoolTrue
  else
    none
  let c_wr? := if range.isFinite && range.nonEmpty && env.contains cwwName then
    some <| mkApp7 (mkConst cwrName [u]) type rangeExpr toIntInst opInst toIntOpInst reflBoolTrue reflBoolTrue
  else
    none
  return { c? := some c, c_ww?, c_wl?, c_wr? }

-- TODO: improve this function
private def evalInt? (e : Expr) : MetaM (Option Int) := do
  let e ← whnfD e
  match_expr e with
  | Int.ofNat a =>
    let some a ← getNatValue? (← whnfD a) | return none
    return some (a : Int)
  | Int.negSucc a =>
    let some a ← getNatValue? (← whnfD a) | return none
    return some (- (a : Int) - 1)
  | _ => return none

def getToIntInfo? (type : Expr) : GoalM (Option ToIntInfo) := do
  if let some id? := (← get').toIntInfos.find? { expr := type } then
    return id?
  else
    let info? ← go?
    modify' fun s => { s with toIntInfos := s.toIntInfos.insert { expr := type } info? }
    return info?
where
  toIntInterval? (rangeExpr : Expr) : GoalM (Option Grind.IntInterval) := do
    let rangeExpr ← whnfD rangeExpr
    match_expr rangeExpr with
    | Grind.IntInterval.co lo hi =>
      let some lo ← evalInt? lo
        | trace[grind.debug.cutsat.toInt] "`ToInt` lower bound could not be reduced to an integer{indentExpr (← whnfD lo)}\nfor type{indentExpr type}"
          return none
      let some hi ← evalInt? hi
        | trace[grind.debug.cutsat.toInt] "`ToInt` upper bound could not be reduced to an integer{indentExpr hi}\nfor type{indentExpr type}"
          return none
      return some (.co lo hi)
    | _ =>
      trace[grind.debug.cutsat.toInt] "unsupported `ToInt` interval{indentExpr rangeExpr}\nfor type{indentExpr type}"
      return none

  go? : GoalM (Option ToIntInfo) := withNewMCtxDepth do
    let u' ← getLevel type
    let u ← decLevel u'
    let rangeExpr ← mkFreshExprMVar (mkConst ``Grind.IntInterval)
    let toIntType := mkApp2 (mkConst ``Grind.ToInt [u]) type rangeExpr
    let .some toIntInst ← trySynthInstance toIntType |
      trace[grind.debug.cutsat.toInt] "failed to synthesize {indentExpr toIntType}"
      return none
    let rangeExpr ← instantiateMVars rangeExpr
    let some range ← toIntInterval? rangeExpr | return none
    let toInt := mkApp3 (mkConst ``Grind.ToInt.toInt [u]) type rangeExpr toIntInst
    let wrap := mkApp (mkConst ``Grind.IntInterval.wrap) rangeExpr
    let ofWrap0? := if let .co 0 hi := range then
      some <| mkApp3 (mkConst ``Grind.ToInt.of_eq_wrap_co_0) rangeExpr (toExpr hi) reflBoolTrue
    else
      none
    let ofEq := mkApp3 (mkConst ``Grind.ToInt.of_eq [u]) type rangeExpr toIntInst
    let ofDiseq := mkApp3 (mkConst ``Grind.ToInt.of_diseq [u]) type rangeExpr toIntInst
    let (ofLE?, ofNotLE?) ← do
      let toLE := mkApp (mkConst ``LE [u]) type
      let .some leInst ← LOption.toOption <$> trySynthInstance toLE | pure (none, none)
      let toIntLE := mkApp4 (mkConst ``Grind.ToInt.LE [u]) type leInst rangeExpr toIntInst
      let .some toIntLEInst ← LOption.toOption <$> trySynthInstance toIntLE
        | reportMissingToIntAdapter type toIntLE; pure (none, none)
      let ofLE := mkApp5 (mkConst ``Grind.ToInt.of_le [u]) type rangeExpr toIntInst leInst toIntLEInst
      let ofNotLE := mkApp5 (mkConst ``Grind.ToInt.of_not_le [u]) type rangeExpr toIntInst leInst toIntLEInst
      pure (some ofLE, some ofNotLE)
    let (ofLT?, ofNotLT?) ← do
      let toLT := mkApp (mkConst ``LT [u]) type
      let .some ltInst ← LOption.toOption <$> trySynthInstance toLT | pure (none, none)
      let toIntLT := mkApp4 (mkConst ``Grind.ToInt.LT [u]) type ltInst rangeExpr toIntInst
      let .some toIntLTInst ← LOption.toOption <$> trySynthInstance toIntLT
        | reportMissingToIntAdapter type toIntLT; pure (none, none)
      let ofLT := mkApp5 (mkConst ``Grind.ToInt.of_lt [u]) type rangeExpr toIntInst ltInst toIntLTInst
      let ofNotLT := mkApp5 (mkConst ``Grind.ToInt.of_not_lt [u]) type rangeExpr toIntInst ltInst toIntLTInst
      pure (some ofLT, some ofNotLT)
    let mkOp (opBaseName : Name) (thmName : Name) :=
      mkOpCongr type u toIntInst rangeExpr range opBaseName thmName
    let add ← mkOp ``Add ``Grind.ToInt.add_congr
    let mul ← mkOp ``Mul ``Grind.ToInt.mul_congr
    -- TODO: other operators
    return some {
      type, u, toIntInst, rangeExpr, range, toInt, wrap, ofWrap0?, ofEq, ofDiseq, ofLE?, ofNotLE?, ofLT?, ofNotLT?, add, mul
    }

structure ToIntM.Context where
  info : ToIntInfo

abbrev ToIntM := ReaderT ToIntM.Context GoalM

def getInfo : ToIntM ToIntInfo :=
  return (← read).info

def ToIntM.run? (type : Expr) (x : ToIntM α) : GoalM (Option α) := do
  let some info ← getToIntInfo? type | return none
  return some (← x { info })

private def isHomo (α β γ : Expr) : Bool :=
  isSameExpr α β && isSameExpr α γ

private def intRfl := mkApp (mkConst ``Eq.refl [1]) Int.mkType

private def toIntDef (e : Expr) : ToIntM (Expr × Expr) := do
  let e' := mkApp (← getInfo).toInt e
  let he := mkApp intRfl e'
  return (e', he)

private def isWrap (e : Expr) : Option Expr :=
  match_expr e with
  | Grind.IntInterval.wrap _ a => some a
  | _ => none

/--
Given `h : toInt a = i.wrap b`, return `(b', h)` where
`b'` is the expanded form of `i.wrap b`, and `h : toInt a = b'`
-/
private def expandWrap (a b : Expr) (h : Expr) : ToIntM (Expr × Expr) := do
  match (← getInfo).range with
  | .ii => return (b, h)
  | .co 0 hi =>
    let b' := mkIntMod b (toExpr hi)
    let toA := mkApp (← getInfo).toInt a
    let h := mkApp3 (← getInfo).ofWrap0?.get! toA b h
    return (b', h)
  | .co lo hi =>
    let b' := mkIntAdd (mkIntMod (mkIntSub b (toExpr lo)) (toExpr (hi - lo))) (toExpr lo)
    return (b', h)
  | _ => throwError "`grind cutsat`, `ToInt` interval not supported yet"

private def mkToIntResult (toIntOp : ToIntCongr) (mkBinOp : Expr → Expr → Expr) (a b : Expr) (a' b' : Expr) (h₁ h₂ : Expr) : ToIntM (Expr × Expr) := do
  let f := toIntOp.c?.get!
  let mk (f : Expr) (a' b' : Expr) : ToIntM (Expr × Expr) := do
    let h := mkApp6 f a b a' b' h₁ h₂
    let r := mkApp (← getInfo).wrap (mkBinOp a' b')
    return (r, h)
  match isWrap a', isWrap b' with
  | none,     none     => mk f a' b'
  | some a'', none     => if let some f := toIntOp.c_wl? then mk f a'' b' else mk f a' b'
  | none,     some b'' => if let some f := toIntOp.c_wr? then mk f a' b'' else mk f a' b'
  | some a'', some b'' => if let some f := toIntOp.c_ww? then mk f a'' b'' else mk f a' b'

partial def toInt (e : Expr) : ToIntM (Expr × Expr) := do
  match_expr e with
  | HAdd.hAdd α β γ _ a b =>
    unless isHomo α β γ do return (← toIntDef e)
    toIntBin (← getInfo).add mkIntAdd a b
  | HMul.hMul α β γ _ a b =>
    unless isHomo α β γ do return (← toIntDef e)
    toIntBin (← getInfo).mul mkIntMul a b
  -- TODO: other operators
  | _ => toIntDef e
where
  toIntBin (toIntOp : ToIntCongr) (mkBinOp : Expr → Expr → Expr) (a b : Expr) : ToIntM (Expr × Expr) := do
    unless toIntOp.c?.isSome do return (← toIntDef e)
    let (a', h₁) ← toInt a
    let (b', h₂) ← toInt b
    mkToIntResult toIntOp mkBinOp a b a' b' h₁ h₂

def toInt? (a : Expr) (type : Expr) : GoalM (Option (Expr × Expr)) := do
  ToIntM.run? type do
    let (b, h) ← toInt a
    match isWrap b with
    | some b' => expandWrap a b' h
    | _ => return (b, h)

end Lean.Meta.Grind.Arith.Cutsat
