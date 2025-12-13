/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Init.Grind.ToIntLemmas
import Init.GrindInstances.ToInt
import Lean.Meta.Tactic.Grind.SynthInstance
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.EvalNum
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
public section
namespace Lean.Meta.Grind.Arith.Cutsat

private def reportMissingToIntAdapter (type : Expr) (instType : Expr) : MetaM Unit := do
  trace[grind.debug.lia.debug] "`ToInt` initialization failure, failed to synthesize{indentExpr instType}\nfor type{indentExpr type}"

private def throwMissingDecl (declName : Name) : MetaM Unit :=
  throwError "`grind cutsat`, unexpected missing declaration {.ofConstName declName}"

private def checkDecl (declName : Name) : MetaM Unit := do
  unless (← getEnv).contains declName do
    throwMissingDecl declName

private def normalizeBound (bound : Expr) : GrindM SymbolicBound := do
  if let some bound ← evalInt? bound then
    return { val := mkIntLit bound, ival? := some bound }
  else
    return { val := bound, ival? := none }

def SymbolicBound.isZero (b : SymbolicBound) : Bool :=
  if let some b := b.ival? then
    b == 0
  else
    false

/-- Given a symbolic bound `b`, returns `-b + 1` -/
def SymbolicBound.mkIntNegSucc (b : SymbolicBound) : MetaM Expr := do
  if let some val := b.ival? then
    return mkIntLit (-val + 1)
  else
    return mkIntAdd (mkIntNeg b.val) (mkIntLit 1)

def getToIntId? (type : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').toIntIds.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with
      toIntIds := s.toIntIds.insert { expr := type } id? }
    return id?
where
  toIntInterval? (rangeExpr : Expr) : GoalM (Option SymbolicIntInterval) := do
    let rangeExpr ← whnfD rangeExpr
    match_expr rangeExpr with
    | Grind.IntInterval.co lo hi =>
      let lo ← normalizeBound lo
      let hi ← normalizeBound hi
      return some (.co lo hi)
    | _ =>
      trace[grind.debug.lia.toInt] "unsupported `ToInt` interval{indentExpr rangeExpr}\nfor type{indentExpr type}"
      return none

  go? : GoalM (Option Nat) := withNewMCtxDepth do
    let u' ← getLevel type
    let some u ← decLevel? u' | return none
    let rangeExpr ← mkFreshExprMVar (mkConst ``Grind.IntInterval)
    let toIntType := mkApp2 (mkConst ``Grind.ToInt [u]) type rangeExpr
    let some toIntInst ← synthInstance? toIntType |
      trace[grind.debug.lia.toInt] "failed to synthesize {indentExpr toIntType}"
      return none
    let rangeExpr ← instantiateMVars rangeExpr
    let some range ← toIntInterval? rangeExpr | return none
    let toInt := mkApp3 (mkConst ``Grind.ToInt.toInt [u]) type rangeExpr toIntInst
    let wrap := mkApp (mkConst ``Grind.IntInterval.wrap) rangeExpr
    let ofWrap0? ← if let .co lo hi := range then
      if lo.isZero then
        pure <| some <| mkApp3 (mkConst ``Grind.ToInt.of_eq_wrap_co_0) rangeExpr hi.val (← mkEqRefl rangeExpr)
      else pure none
      else pure none
    let ofEq := mkApp3 (mkConst ``Grind.ToInt.of_eq [u]) type rangeExpr toIntInst
    let ofDiseq := mkApp3 (mkConst ``Grind.ToInt.of_diseq [u]) type rangeExpr toIntInst
    let lowerThm? ← if let some lo := range.lo? then
      if let some lo' := lo.ival? then
        if lo' == 0 then
          pure <| some <| mkApp4 (mkConst ``Grind.ToInt.ge_lower0 [u]) type rangeExpr toIntInst eagerReflBoolTrue
        else
          pure <| some <| mkApp5 (mkConst ``Grind.ToInt.ge_lower [u]) type rangeExpr toIntInst lo.val eagerReflBoolTrue
      else
        -- Symbolic case
        let some_lo ← mkSome Int.mkType lo.val
        pure <| some <| mkApp5 (mkConst ``Grind.ToInt.ge_lower' [u]) type rangeExpr toIntInst lo.val (← mkEqRefl some_lo)
    else pure none
    let upperThm? ← if let some hi := range.hi? then
      if hi.isNumeral then
        pure <| some <| mkApp5 (mkConst ``Grind.ToInt.le_upper [u]) type rangeExpr toIntInst (← hi.mkIntNegSucc) eagerReflBoolTrue
      else
        -- Symbolic case
        let some_hi ← mkSome Int.mkType hi.val
        pure <| some <| mkApp5 (mkConst ``Grind.ToInt.le_upper' [u]) type rangeExpr toIntInst hi.val (← mkEqRefl some_hi)
    else pure none
    trace[grind.debug.lia.toInt] "registered toInt: {type}"
    let id := (← get').toIntInfos.size
    modify' fun s => { s with toIntInfos := s.toIntInfos.push { id, type, u, toIntInst, rangeExpr, range, toInt, wrap, ofWrap0?, ofEq, ofDiseq, lowerThm?, upperThm? } }
    return some id

structure ToIntM.Context where
  toIntId : Nat

abbrev ToIntM := ReaderT ToIntM.Context GoalM

def getToIntId : ToIntM Nat :=
  return (← read).toIntId

def getInfo : ToIntM ToIntInfo :=
  return (← get').toIntInfos[(← getToIntId)]!

abbrev modifyInfo (f : ToIntInfo → ToIntInfo) : ToIntM Unit := do
  let id ← getToIntId
  modify' fun s => { s with toIntInfos := s.toIntInfos.modify id f }

def ToIntM.run? (type : Expr) (x : ToIntM α) : GoalM (Option α) := do
  let some toIntId ← getToIntId? type | return none
  return some (← x { toIntId })

def ToIntM.run (type : Expr) (x : ToIntM Unit) : GoalM Unit := do
  let some toIntId ← getToIntId? type | return ()
  x { toIntId }

private def intRfl := mkApp (mkConst ``Eq.refl [1]) Int.mkType

private def mkOfLE : ToIntM (Option Expr × Option Expr) := do
  let info ← getInfo
  let toLE := mkApp (mkConst ``LE [info.u]) info.type
  let some leInst ← synthInstance? toLE | return (none, none)
  let toIntLE := mkApp4 (mkConst ``Grind.ToInt.LE [info.u]) info.type leInst info.rangeExpr info.toIntInst
  let some toIntLEInst ← synthInstance? toIntLE
    | reportMissingToIntAdapter info.type toIntLE; return (none, none)
  let ofLE := mkApp5 (mkConst ``Grind.ToInt.of_le [info.u]) info.type info.rangeExpr info.toIntInst leInst toIntLEInst
  let ofNotLE := mkApp5 (mkConst ``Grind.ToInt.of_not_le [info.u]) info.type info.rangeExpr info.toIntInst leInst toIntLEInst
  return (some ofLE, some ofNotLE)

def getOfLE? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).ofLE? then return r?
  let (ofLE?, ofNotLE?) ← mkOfLE
  modifyInfo fun s => { s with ofLE? := some ofLE?, ofNotLE? := some ofNotLE? }
  return ofLE?

def getOfNotLE? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).ofNotLE? then return r?
  let (ofLE?, ofNotLE?) ← mkOfLE
  modifyInfo fun s => { s with ofLE? := some ofLE?, ofNotLE? := some ofNotLE? }
  return ofNotLE?

private def mkOfLT : ToIntM (Option Expr × Option Expr) := do
  let info ← getInfo
  let toLT := mkApp (mkConst ``LT [info.u]) info.type
  let some ltInst ← synthInstance? toLT | return (none, none)
  let toIntLT := mkApp4 (mkConst ``Grind.ToInt.LT [info.u]) info.type ltInst info.rangeExpr info.toIntInst
  let some toIntLTInst ← synthInstance? toIntLT
    | reportMissingToIntAdapter info.type toIntLT; return (none, none)
  let ofLT := mkApp5 (mkConst ``Grind.ToInt.of_lt [info.u]) info.type info.rangeExpr info.toIntInst ltInst toIntLTInst
  let ofNotLT := mkApp5 (mkConst ``Grind.ToInt.of_not_lt [info.u]) info.type info.rangeExpr info.toIntInst ltInst toIntLTInst
  return (some ofLT, some ofNotLT)

def getOfLT? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).ofLT? then return r?
  let (ofLT?, ofNotLT?) ← mkOfLT
  modifyInfo fun s => { s with ofLT? := some ofLT?, ofNotLT? := some ofNotLT? }
  return ofLT?

def getOfNotLT? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).ofNotLT? then return r?
  let (ofLT?, ofNotLT?) ← mkOfLT
  modifyInfo fun s => { s with ofLT? := some ofLT?, ofNotLT? := some ofNotLT? }
  return ofNotLT?

/-- Helper function for `mkSimpleOpThm?` and `mkPowThm?` -/
private def mkSimpleOpThmCore? (op : Expr) (opSuffix : Name) (thmName : Name) : ToIntM (Option Expr) := do
  let some opInst ← synthInstance? op | return none
  let toIntOpName := ``Grind.ToInt ++ opSuffix
  checkDecl toIntOpName
  let info ← getInfo
  let toIntOp := mkApp4 (mkConst toIntOpName [info.u]) info.type opInst info.rangeExpr info.toIntInst
  let some toIntOpInst ← synthInstance? toIntOp
    | reportMissingToIntAdapter info.type toIntOp; return none
  checkDecl thmName
  return mkApp5 (mkConst thmName [info.u]) info.type info.rangeExpr info.toIntInst opInst toIntOpInst

/-- Simpler version of `mkBinOpThms` for operators that have only one congruence theorem. -/
private def mkSimpleOpThm? (opBaseName : Name) (thmName : Name) : ToIntM (Option Expr) := do
  let info ← getInfo
  let op := mkApp (mkConst opBaseName [info.u]) info.type
  mkSimpleOpThmCore? op opBaseName thmName

/-- Simpler version of `mkBinOpThms` for operators that have only one congruence theorem. -/
private def mkPowThm? : ToIntM (Option Expr) := do
  let info ← getInfo
  let op := mkApp3 (mkConst ``HPow [info.u, 0, info.u]) info.type Nat.mkType info.type
  mkSimpleOpThmCore? op `Pow ``Grind.ToInt.pow_congr

private def mkBinOpThms (opBaseName : Name) (thmName : Name) : ToIntM ToIntThms := do
  let some c ← mkSimpleOpThm? opBaseName thmName | return {}
  let opInst := c.appFn!.appArg!
  let toIntOpInst := c.appArg!
  let env ← getEnv
  let cwwName := thmName ++ `ww
  let cwlName := thmName ++ `wl
  let cwrName := thmName ++ `wr
  let info ← getInfo
  let c_ww? := if info.range.isFinite && env.contains cwwName then
    some <| mkApp6 (mkConst cwwName [info.u]) info.type info.rangeExpr info.toIntInst opInst toIntOpInst eagerReflBoolTrue
  else
    none
  let c_wl? := if info.range.isFinite && env.contains cwlName then
    some <| mkApp6 (mkConst cwlName [info.u]) info.type info.rangeExpr info.toIntInst opInst toIntOpInst eagerReflBoolTrue
  else
    none
  let c_wr? := if info.range.isFinite && env.contains cwrName then
    some <| mkApp6 (mkConst cwrName [info.u]) info.type info.rangeExpr info.toIntInst opInst toIntOpInst eagerReflBoolTrue
  else
    none
  return { c? := some c, c_ww?, c_wl?, c_wr? }

def getAddThms : ToIntM ToIntThms := do
  if let some r := (← getInfo).addThms? then return r
  let thms ← mkBinOpThms ``Add ``Grind.ToInt.add_congr
  modifyInfo fun s => { s with addThms? := some thms }
  return thms

def getMulThms : ToIntM ToIntThms := do
  if let some r := (← getInfo).mulThms? then return r
  let thms ← mkBinOpThms ``Mul ``Grind.ToInt.mul_congr
  modifyInfo fun s => { s with mulThms? := some thms }
  return thms

def getSubThm? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).subThm? then return r?
  let thm? ← mkSimpleOpThm? ``Sub ``Grind.ToInt.sub_congr
  modifyInfo fun s => { s with subThm? := some thm? }
  return thm?

def getNegThm? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).negThm? then return r?
  let thm? ← mkSimpleOpThm? ``Neg ``Grind.ToInt.neg_congr
  modifyInfo fun s => { s with negThm? := some thm? }
  return thm?

def getDivThm? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).divThm? then return r?
  let thm? ← mkSimpleOpThm? ``Div ``Grind.ToInt.div_congr
  modifyInfo fun s => { s with divThm? := some thm? }
  return thm?

def getModThm? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).modThm? then return r?
  let thm? ← mkSimpleOpThm? ``Mod ``Grind.ToInt.mod_congr
  modifyInfo fun s => { s with modThm? := some thm? }
  return thm?

def getPowThm? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).powThm? then return r?
  let thm? ← mkPowThm?
  modifyInfo fun s => { s with powThm? := some thm? }
  return thm?

def getZeroThm? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).zeroThm? then return r?
  let thm? ← mkSimpleOpThm? ``Zero ``Grind.ToInt.zero_eq
  modifyInfo fun s => { s with zeroThm? := some thm? }
  return thm?

private def mkOfNatThm? : ToIntM (Option Expr) := do
  -- ∀ n, OfNat α n
  let info ← getInfo
  let ofNat := mkForall `n .default (mkConst ``Nat) (mkApp2 (mkConst ``OfNat [info.u]) info.type (mkBVar 0))
  let some ofNatInst ← synthInstance? ofNat
    | reportMissingToIntAdapter info.type ofNat; return none
  let toIntOfNat := mkApp4 (mkConst ``Grind.ToInt.OfNat [info.u]) info.type ofNatInst info.rangeExpr info.toIntInst
  let some toIntOfNatInst ← synthInstance? toIntOfNat
    | reportMissingToIntAdapter info.type toIntOfNat; return none
  return mkApp5 (mkConst ``Grind.ToInt.ofNat_eq [info.u]) info.type info.rangeExpr info.toIntInst ofNatInst toIntOfNatInst

def getOfNatThm? : ToIntM (Option Expr) := do
  if let some r? := (← getInfo).ofNatThm? then return r?
  let thm? ← mkOfNatThm?
  modifyInfo fun s => { s with ofNatThm? := some thm? }
  return thm?

def mkToIntVar (e : Expr) : ToIntM (Expr × Expr) := do
  if let some info := (← get').toIntTermMap.find? { expr := e } then
    return (info.eToInt, info.he)
  let eToInt := mkApp (← getInfo).toInt e
  let he := mkApp intRfl eToInt
  let α := (← getInfo).type
  modify' fun s => { s with
    toIntTermMap := s.toIntTermMap.insert { expr := e } { eToInt, he, α }
  }
  cutsatExt.markTerm e
  return (eToInt, he)

def getToIntTermType? (e : Expr) : GoalM (Option Expr) := do
  let some info := (← get').toIntTermMap.find? { expr := e } | return none
  return some info.α

def isToIntTerm (e : Expr) : GoalM Bool :=
  return (← get').toIntTermMap.contains { expr := e }

private def isHomo (α β γ : Expr) : Bool :=
  isSameExpr α β && isSameExpr α γ

private def isWrap (e : Expr) : Option Expr :=
  match_expr e with
  | Grind.IntInterval.wrap _ a => some a
  | _ => none

private def hasNumericLoHi : ToIntM Bool := do
  let info ← getInfo
  let some lo := info.range.lo? | return false
  let some hi := info.range.hi? | return false
  return lo.isNumeral && hi.isNumeral

/--
Given `h : toInt a = i.wrap b`, return `(b', h)` where
`b'` is the expanded form of `i.wrap b`, and `h : toInt a = b'`
-/
private def expandWrap (a b : Expr) (h : Expr) : ToIntM (Expr × Expr) := do
  let range := (← getInfo).range
  match range with
  | .ii => return (b, h)
  | .co lo hi =>
    if lo.isZero then
      let b' := mkIntMod b hi.val
      let toA := mkApp (← getInfo).toInt a
      let h := mkApp3 (← getInfo).ofWrap0?.get! toA b h
      if hi.isNumeral then
        return (b', h)
      else
        -- We must preprocess `b'` because `hi` has not been normalized and may interact with `%`
        let r ← preprocess b'
        let h ← mkEqTrans h (← r.getProof)
        let b' := r.expr
        internalize b' (← getGeneration b)
        return (b', h)
    else
      let b' ← range.wrap b
      if (← hasNumericLoHi) then
        return (b', h)
      else
        -- We must preprocess `b'` because `lo` and/or `hi` are symbolic values that may
        -- interact with the wrap operations and have not been normalized yet.
        let r ← preprocess b'
        let h ← mkEqTrans h (← r.getProof)
        let b' := r.expr
        internalize b' (← getGeneration b)
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

/-- Returns `some (n, neZeroInst)` if `inst` is of the form `Fin.instOfNat n neZeroInst _` -/
private def isFinInstOfNat? (inst : Expr) : MetaM (Option (Expr × Expr)) := do
  let_expr Fin.instOfNat n neZeroInst _ := inst | return none
  return some (n, neZeroInst)

private partial def toInt' (e : Expr) : ToIntM (Expr × Expr) := do
  match_expr e with
  | HAdd.hAdd α β γ _ a b =>
    unless isHomo α β γ do return (← mkToIntVar e)
    toIntBin (← getAddThms) mkIntAdd a b
  | HMul.hMul α β γ _ a b =>
    unless isHomo α β γ do return (← mkToIntVar e)
    toIntBin (← getMulThms) mkIntMul a b
  | HDiv.hDiv α β γ _ a b =>
    unless isHomo α β γ do return (← mkToIntVar e)
    processDivMod (isDiv := true) a b
  | HMod.hMod α β γ _ a b =>
    unless isHomo α β γ do return (← mkToIntVar e)
    processDivMod (isDiv := false) a b
  | HSub.hSub α β γ _ a b =>
    unless isHomo α β γ do return (← mkToIntVar e)
    processSub a b
  | Neg.neg _ _ a =>
    processNeg a
  | HPow.hPow α β γ _ a b =>
    unless isSameExpr α γ && β.isConstOf ``Nat do return (← mkToIntVar e)
    processPow a b
  | Zero.zero _ _ =>
    let some thm ← getZeroThm? | mkToIntVar e
    return (mkIntLit 0, thm)
  | OfNat.ofNat _ n inst =>
    let some n ← getNatValue? n | mkToIntVar e
    if n == 0 then
      if let some (k, neZeroInst) ← isFinInstOfNat? inst then
        let h := mkApp2 (mkConst ``Lean.Grind.ofNat_FinZero) k neZeroInst
        return (mkIntLit 0, h)
    toIntOfNat e n
  | BitVec.ofNat _ n =>
    let some n ← getNatValue? n | mkToIntVar e
    toIntOfNat e n
  | _ => mkToIntVar e
where
  toIntOfNat (e : Expr) (n : Nat) : ToIntM (Expr × Expr) := do
    let some thm ← getOfNatThm? | mkToIntVar e
    let h := mkApp thm (toExpr n)
    if (← hasNumericLoHi) then
      let r ← (← getInfo).range.wrap (mkIntLit n)
      return (r, h)
    else
      expandWrap e (mkIntLit n) h

  toIntBin (toIntOp : ToIntThms) (mkBinOp : Expr → Expr → Expr) (a b : Expr) : ToIntM (Expr × Expr) := do
    unless toIntOp.c?.isSome do return (← mkToIntVar e)
    let (a', h₁) ← toInt' a
    let (b', h₂) ← toInt' b
    toIntOp.mkResult mkBinOp a b a' b' h₁ h₂

  toIntAndExpandWrap (a : Expr) : ToIntM (Expr × Expr) := do
    let (a', h₁) ← toInt' a
    expandIfWrap a a' h₁

  processDivMod (isDiv : Bool) (a b : Expr) : ToIntM (Expr × Expr) := do
    let some thm ← if isDiv then getDivThm? else getModThm?
      | return (← mkToIntVar e)
    let (a', h₁) ← toIntAndExpandWrap a
    let (b', h₂) ← toIntAndExpandWrap b
    let r := if isDiv then mkIntDiv a' b' else mkIntMod a' b'
    let h := mkApp6 thm a b a' b' h₁ h₂
    return (r, h)

  processSub (a b : Expr) : ToIntM (Expr × Expr) := do
    let some thm ← getSubThm? | mkToIntVar e
    let (a', h₁) ← toIntAndExpandWrap a
    let (b', h₂) ← toIntAndExpandWrap b
    let r ← mkWrap (mkIntSub a' b')
    let h := mkApp6 thm a b a' b' h₁ h₂
    return (r, h)

  processNeg (a : Expr) : ToIntM (Expr × Expr) := do
    let some thm ← getNegThm? | mkToIntVar e
    let (a', h₁) ← toIntAndExpandWrap a
    let r ← mkWrap (mkIntNeg a')
    let h := mkApp3 thm a a' h₁
    return (r, h)

  processPow (a b : Expr) : ToIntM (Expr × Expr) := do
    let some thm ← getPowThm? | mkToIntVar e
    let (a', h₁) ← toIntAndExpandWrap a
    let r ← mkWrap (mkIntPowNat a' b)
    let h := mkApp4 thm a b a' h₁
    return (r, h)

def toInt (a : Expr) : ToIntM (Expr × Expr) := do
  let (b, h) ← toInt' a
  let (b, h) ← match isWrap b with
    | some b' => expandWrap a b' h
    | _ => pure (b, h)
  let r ← preprocess b
  if let some proof := r.proof? then
    return (r.expr, (← mkEqTrans h proof))
  else
    return (r.expr, h)

def toInt? (a : Expr) (type : Expr) : GoalM (Option (Expr × Expr)) := do
  ToIntM.run? type do toInt a

def isSupportedType (type : Expr) : GoalM Bool := do
  if type == Nat.mkType || type == Int.mkType then
    return true
  else
    return (← getToIntId? type).isSome

/--
Given `x` whose denotation is `e`, if `e` is of the form `ToInt a`,
asserts its lower and upper bounds if available
-/
def assertToIntBounds (e : Expr) (x : Var) : GoalM Unit := do
  let_expr Grind.ToInt.toInt α _ _ a := e | return ()
  ToIntM.run α do
  let info ← getInfo
  let i := info.range
  if let some lo := i.lo? then
    let some thm := info.lowerThm? | unreachable!
    if let some lo := lo.ival? then
      let p := .add (-1) x (.num lo)
      let c := { p, h := .bound (mkApp thm a) : LeCnstr }
      c.assert
    else
      pushNewFact <| mkApp thm a
  if let some hi := i.hi? then
    let some thm := info.upperThm? | unreachable!
    if let some hi := hi.ival? then
      let p := .add 1 x (.num (-hi + 1))
      let c := { p, h := .bound (mkApp thm a) : LeCnstr }
      c.assert
    else
      pushNewFact <| mkApp thm a

end Lean.Meta.Grind.Arith.Cutsat
