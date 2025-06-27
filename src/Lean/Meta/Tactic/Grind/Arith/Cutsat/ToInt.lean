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

private def mkOfNatThm? (type : Expr) (u : Level) (toIntInst : Expr) (rangeExpr : Expr) : MetaM (Option Expr) := do
  -- ∀ n, OfNat α n
  let ofNat := mkForall `n .default (mkConst ``Nat) (mkApp2 (mkConst ``OfNat [u]) type (mkBVar 0))
  let .some ofNatInst ← trySynthInstance ofNat
    | reportMissingToIntAdapter type ofNat; return none
  let toIntOfNat := mkApp4 (mkConst ``Grind.ToInt.OfNat [u]) type ofNatInst rangeExpr toIntInst
  let .some toIntOfNatInst ← trySynthInstance toIntOfNat
    | reportMissingToIntAdapter type toIntOfNat; return none
  return mkApp5 (mkConst ``Grind.ToInt.ofNat_eq [u]) type rangeExpr toIntInst ofNatInst toIntOfNatInst

/-- Helper function for `mkSimpleOpThm?` and `mkPowThm?` -/
private def mkSimpleOpThmCore? (type : Expr) (u : Level) (toIntInst : Expr) (rangeExpr : Expr) (op : Expr) (opSuffix : Name) (thmName : Name) : MetaM (Option Expr) := do
  let .some opInst ← trySynthInstance op | return none
  let toIntOpName := ``Grind.ToInt ++ opSuffix
  checkDecl toIntOpName
  let toIntOp := mkApp4 (mkConst toIntOpName [u]) type opInst rangeExpr toIntInst
  let .some toIntOpInst ← trySynthInstance toIntOp
    | reportMissingToIntAdapter type toIntOp; return none
  checkDecl thmName
  return mkApp5 (mkConst thmName [u]) type rangeExpr toIntInst opInst toIntOpInst

/-- Simpler version of `mkBinOpThms` for operators that have only one congruence theorem. -/
private def mkSimpleOpThm? (type : Expr) (u : Level) (toIntInst : Expr) (rangeExpr : Expr) (opBaseName : Name) (thmName : Name) : MetaM (Option Expr) := do
  let op := mkApp (mkConst opBaseName [u]) type
  mkSimpleOpThmCore? type u toIntInst rangeExpr op opBaseName thmName

/-- Simpler version of `mkBinOpThms` for operators that have only one congruence theorem. -/
private def mkPowThm? (type : Expr) (u : Level) (toIntInst : Expr) (rangeExpr : Expr) : MetaM (Option Expr) := do
  let op := mkApp3 (mkConst ``HPow [u, 0, u]) type Nat.mkType type
  mkSimpleOpThmCore? type u toIntInst rangeExpr op `Pow ``Grind.ToInt.pow_congr

private def mkBinOpThms (type : Expr) (u : Level) (toIntInst : Expr) (rangeExpr : Expr) (range : Grind.IntInterval) (opBaseName : Name) (thmName : Name) : MetaM ToIntThms := do
  let some c ← mkSimpleOpThm? type u toIntInst rangeExpr opBaseName thmName | return {}
  let opInst := c.appFn!.appArg!
  let toIntOpInst := c.appArg!
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
    let mkBinOpThms (opBaseName : Name) (thmName : Name) :=
      mkBinOpThms type u toIntInst rangeExpr range opBaseName thmName
    let mkSimpleOpThm? (opBaseName : Name) (thmName : Name) :=
      mkSimpleOpThm? type u toIntInst rangeExpr opBaseName thmName
    let addThms ← mkBinOpThms ``Add ``Grind.ToInt.add_congr
    let mulThms ← mkBinOpThms ``Mul ``Grind.ToInt.mul_congr
    let subThm? ← mkSimpleOpThm? ``Sub ``Grind.ToInt.sub_congr
    let negThm? ← mkSimpleOpThm? ``Neg ``Grind.ToInt.neg_congr
    let divThm? ← mkSimpleOpThm? ``Div ``Grind.ToInt.div_congr
    let modThm? ← mkSimpleOpThm? ``Mod ``Grind.ToInt.mod_congr
    let powThm? ← mkPowThm? type u toIntInst rangeExpr
    let zeroThm? ← mkSimpleOpThm? ``Zero ``Grind.ToInt.zero_eq
    let ofNatThm? ← mkOfNatThm? type u toIntInst rangeExpr
    return some {
      type, u, toIntInst, rangeExpr, range, toInt, wrap, ofWrap0?, ofEq, ofDiseq, ofLE?, ofNotLE?, ofLT?, ofNotLT?, addThms, mulThms,
      subThm?, negThm?, divThm?, modThm?, powThm?, zeroThm?, ofNatThm?
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

/--
Given `h : toInt a = b`, if `b` is of the form `i.wrap b'`,
invokes `expandWrap a b' h`
-/
private def expandIfWrap (a b : Expr) (h : Expr) : ToIntM (Expr × Expr) := do
  match isWrap b with
  | none => return (b, h)
  | some b => expandWrap a b h

private def mkWrap (a : Expr) : ToIntM Expr := do
  return mkApp (← getInfo).wrap a

private def ToIntThms.mkResult (toIntThms : ToIntThms) (mkBinOp : Expr → Expr → Expr) (a b : Expr) (a' b' : Expr) (h₁ h₂ : Expr) : ToIntM (Expr × Expr) := do
  let f := toIntThms.c?.get!
  let mk (f : Expr) (a' b' : Expr) : ToIntM (Expr × Expr) := do
    -- If the appropriate `wrap` cancellation theorem is missing, we have to expand the nested wrap.
    let (a', h₁) ← expandIfWrap a a' h₁
    let (b', h₂) ← expandIfWrap b b' h₂
    let h := mkApp6 f a b a' b' h₁ h₂
    let r ← mkWrap (mkBinOp a' b')
    return (r, h)
  match isWrap a', isWrap b' with
  | none,     none     => mk f a' b'
  | some a'', none     => if let some f := toIntThms.c_wl? then mk f a'' b' else mk f a' b'
  | none,     some b'' => if let some f := toIntThms.c_wr? then mk f a' b'' else mk f a' b'
  | some a'', some b'' => if let some f := toIntThms.c_ww? then mk f a'' b'' else mk f a' b'

partial def toInt (e : Expr) : ToIntM (Expr × Expr) := do
  match_expr e with
  | HAdd.hAdd α β γ _ a b =>
    unless isHomo α β γ do return (← toIntDef e)
    toIntBin (← getInfo).addThms mkIntAdd a b
  | HMul.hMul α β γ _ a b =>
    unless isHomo α β γ do return (← toIntDef e)
    toIntBin (← getInfo).mulThms mkIntMul a b
  | HDiv.hDiv α β γ _ a b =>
    unless isHomo α β γ do return (← toIntDef e)
    processDivMod (isDiv := true) a b
  | HMod.hMod α β γ _ a b =>
    unless isHomo α β γ do return (← toIntDef e)
    processDivMod (isDiv := false) a b
  | HSub.hSub α β γ _ a b =>
    unless isHomo α β γ do return (← toIntDef e)
    processSub a b
  | Neg.neg _ _ a =>
    processNeg a
  | HPow.hPow α β γ _ a b =>
    unless isSameExpr α γ && β.isConstOf ``Nat do return (← toIntDef e)
    processPow a b
  | Zero.zero _ _ =>
    let some thm := (← getInfo).zeroThm? | toIntDef e
    return (mkIntLit 0, thm)
  | OfNat.ofNat _ n _ =>
    let some thm := (← getInfo).ofNatThm? | toIntDef e
    let some n ← getNatValue? n | toIntDef e
    let r := mkIntLit ((← getInfo).range.wrap n)
    let h := mkApp thm (toExpr n)
    return (r, h)
  | _ => toIntDef e
where
  toIntBin (toIntOp : ToIntThms) (mkBinOp : Expr → Expr → Expr) (a b : Expr) : ToIntM (Expr × Expr) := do
    unless toIntOp.c?.isSome do return (← toIntDef e)
    let (a', h₁) ← toInt a
    let (b', h₂) ← toInt b
    toIntOp.mkResult mkBinOp a b a' b' h₁ h₂

  toIntAndExpandWrap (a : Expr) : ToIntM (Expr × Expr) := do
    let (a', h₁) ← toInt a
    expandIfWrap a a' h₁

  processDivMod (isDiv : Bool) (a b : Expr) : ToIntM (Expr × Expr) := do
    let some thm ← if isDiv then pure (← getInfo).divThm? else pure (← getInfo).modThm?
      | return (← toIntDef e)
    let (a', h₁) ← toIntAndExpandWrap a
    let (b', h₂) ← toIntAndExpandWrap b
    let r := if isDiv then mkIntDiv a' b' else mkIntMod a' b'
    let h := mkApp6 thm a b a' b' h₁ h₂
    return (r, h)

  processSub (a b : Expr) : ToIntM (Expr × Expr) := do
    let some thm := (← getInfo).subThm? | return (← toIntDef e)
    let (a', h₁) ← toIntAndExpandWrap a
    let (b', h₂) ← toIntAndExpandWrap b
    let r ← mkWrap (mkIntSub a' b')
    let h := mkApp6 thm a b a' b' h₁ h₂
    return (r, h)

  processNeg (a : Expr) : ToIntM (Expr × Expr) := do
    let some thm := (← getInfo).negThm? | return (← toIntDef e)
    let (a', h₁) ← toIntAndExpandWrap a
    let r ← mkWrap (mkIntNeg a')
    let h := mkApp3 thm a a' h₁
    return (r, h)

  processPow (a b : Expr) : ToIntM (Expr × Expr) := do
    let some thm := (← getInfo).powThm? | return (← toIntDef e)
    let (a', h₁) ← toIntAndExpandWrap a
    let r ← mkWrap (mkIntPowNat a' b)
    let h := mkApp4 thm a b a' h₁
    return (r, h)

def toInt? (a : Expr) (type : Expr) : GoalM (Option (Expr × Expr)) := do
  ToIntM.run? type do
    let (b, h) ← toInt a
    match isWrap b with
    | some b' => expandWrap a b' h
    | _ => return (b, h)

end Lean.Meta.Grind.Arith.Cutsat
