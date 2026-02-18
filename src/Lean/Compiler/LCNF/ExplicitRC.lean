/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PhaseExt
import Lean.Runtime
import Lean.Compiler.LCNF.PrettyPrinter

namespace Lean.Compiler.LCNF

open ImpureType


/-!
The following section is the derived value analysis. It figures out parent values for variables that
were created using various forms of projections (currently `oproj` and `Array` accesses). This
information is later used to reduce reference counting pressure.
-/

/--
Contains information about values derived through various forms of projection from other values.
-/
structure DerivedValInfo where
  /--
  The variable this value was derived from. This is always set except for parameters as they have no
  value to be derived from.
  -/
  parent? : Option FVarId
  /--
  The set of variables that were derived from this value.
  -/
  children : FVarIdHashSet
  deriving Inhabited

abbrev DerivedValMap := Std.HashMap FVarId DerivedValInfo

namespace CollectDerivedValInfo

structure State where
  varMap : DerivedValMap := {}
  borrowedParams : FVarIdHashSet := {}

abbrev M := StateRefT State CompilerM

def visitParam (p : Param .impure) : M Unit :=
  modify fun s => { s with
    varMap := s.varMap.insert p.fvarId {
      parent? := none
      children := {}
    }
    borrowedParams :=
      if p.borrow && p.type.isPossibleRef then
        s.borrowedParams.insert p.fvarId
      else
        s.borrowedParams
  }

partial def addDerivedValue (parent : FVarId) (child : FVarId) : M Unit := do
  modify fun s => { s with
    varMap := s.varMap.modify parent fun info =>
      { info with children := info.children.insert child }
  }
  modify fun s => { s with
    varMap := s.varMap.insert child {
      parent? := some parent
      children := {}
    }
  }

partial def removeFromParent (child : FVarId) : M Unit := do
  if let (some parent) := (← get).varMap.get? child |>.bind (·.parent?) then
    modify fun s => { s with
      varMap := s.varMap.modify parent fun info =>
        { info with children := info.children.erase child }
    }

partial def collectCode (code : Code .impure) : M Unit := do
  match code with
  | .let decl k =>
    match decl.value with
    | .oproj _ parent =>
      addDerivedValue parent decl.fvarId
    | .fap ``Array.getInternal args =>
      if let .fvar parent := args[1]! then
        addDerivedValue parent decl.fvarId
    | .fap ``Array.get!Internal args =>
      if let .fvar parent := args[2]! then
        addDerivedValue parent decl.fvarId
    | .reset _ target =>
      removeFromParent target
    | _ => pure ()
    collectCode k
  | .jp decl k =>
    decl.params.forM visitParam
    collectCode decl.value
    collectCode k
  | .cases cases => cases.alts.forM (·.forCodeM collectCode)
  | .sset (k := k) .. | .uset (k := k) .. => collectCode k
  | .return .. | .jmp .. | .unreach .. => return ()
  | .inc .. | .dec .. => unreachable!

def collect (ps : Array (Param .impure)) (code : Code .impure) :
    CompilerM (DerivedValMap × FVarIdHashSet) := do
  let ⟨_, { varMap, borrowedParams }⟩ ← go |>.run {}
  return ⟨varMap, borrowedParams⟩
where
  go : M Unit := do
    ps.forM visitParam
    collectCode code

end CollectDerivedValInfo

structure VarInfo where
  isPossibleRef : Bool
  isDefiniteRef : Bool
  persistent : Bool
  idx : Nat
  deriving Inhabited

abbrev VarMap := FVarIdMap VarInfo

structure LiveVars where
  vars : FVarIdSet := {}
  borrows : FVarIdSet := {}
  deriving Inhabited

@[inline]
def LiveVars.merge (liveVars1 liveVars2 : LiveVars) : LiveVars :=
  let vars := liveVars1.vars.merge liveVars2.vars
  let borrows := liveVars1.borrows.merge liveVars2.borrows
  { vars, borrows }

@[inline]
def LiveVars.erase (liveVars : LiveVars) (fvarId : FVarId) : LiveVars :=
  let vars := liveVars.vars.erase fvarId
  let borrows := liveVars.borrows.erase fvarId
  { vars, borrows }

abbrev JPLiveVarMap := FVarIdMap LiveVars

structure Context where
  borrowedParams : FVarIdHashSet
  derivedValMap : DerivedValMap
  varMap : VarMap := {}
  jpLiveVarMap : JPLiveVarMap := {}
  idx : Nat := 0
  decls : Array (Decl .impure)

structure State where
  liveVars : LiveVars := {}

abbrev RcM := ReaderT Context <| StateRefT State CompilerM

@[inline]
def getVarInfo (fvarId : FVarId) : RcM VarInfo := return (← read).varMap.get! fvarId

@[inline]
def getJpLiveVars (fvarId : FVarId) : RcM LiveVars := return (← read).jpLiveVarMap.get! fvarId

@[inline]
def isLive (fvarId : FVarId) : RcM Bool := return (← get).liveVars.vars.contains fvarId

@[inline]
def isBorrowed (fvarId : FVarId) : RcM Bool := return (← get).liveVars.borrows.contains fvarId

def getDeclSig (declName : Name) : RcM (Option (Signature .impure)) := do
  match (← read).decls.find? (·.name == declName) with
  | some found => return some <| found.toSignature
  | none => getImpureSignature? declName

@[inline]
def withParams (ps : Array (Param .impure)) (x : RcM α) : RcM α := do
  let update := fun ctx =>
    ps.foldl (init := ctx) fun ctx p =>
      let varMap := ctx.varMap.insert p.fvarId {
        isPossibleRef := p.type.isPossibleRef
        isDefiniteRef := p.type.isDefiniteRef
        persistent := false
        idx := ctx.idx,
      }
      { ctx with idx := ctx.idx + 1, varMap }
  withReader update x

def LetValue.isPersistent (val : LetValue .impure) : Bool :=
  match val with
  | .fap _ xs => xs.isEmpty -- all global constants are persistent
  | _ => false

-- TODO: This heuristic should never be necessary
def refineTypeForExpr (value : LetValue .impure) (origt : Expr) : Expr :=
  if origt.isScalar then
    origt
  else
    match value with
    | .ctor c _ => c.type
    | .lit (.nat n) =>
      if n ≤ maxSmallNat then
        tagged
      else
        origt
    | _ => origt

@[inline]
def withLetDecl (decl : LetDecl .impure) (x : RcM α) : RcM α := do
  let update := fun ctx =>
    let type := refineTypeForExpr decl.value decl.type
    let varInfo := {
      isPossibleRef := type.isPossibleRef
      isDefiniteRef := type.isDefiniteRef
      persistent := decl.value.isPersistent
      idx := ctx.idx
    }
    { ctx with varMap := ctx.varMap.insert decl.fvarId varInfo, idx := ctx.idx + 1 }
  withReader update do
    x

@[inline]
def withCtorAlt (discr : FVarId) (c : CtorInfo) (x : RcM α) : RcM α := do
  withReader
    (fun ctx =>
      { ctx with
        varMap :=
          match ctx.varMap.get? discr with
          | some info =>
            let isPossibleRef := c.type.isPossibleRef
            let isDefiniteRef := c.type.isDefiniteRef
            ctx.varMap.insert discr { info with isPossibleRef, isDefiniteRef, idx := ctx.idx + 1 }
          | none => ctx.varMap
        idx := ctx.idx + 1
      }) do x

def setLiveVars (liveVars : LiveVars) : RcM Unit :=
  modify fun s => { s with liveVars }

@[inline]
def withCollectLiveVars (x : RcM α) : RcM (α × LiveVars) := do
  let currentLiveVars := (← get).liveVars
  modify fun s => { s with liveVars := {} }
  let ret ← x
  let collected := (← get).liveVars
  modify fun s => { s with liveVars := currentLiveVars }
  return (ret, collected)

@[specialize]
partial def addDescendants (fvarId : FVarId) (s : FVarIdSet)
    (shouldAdd : FVarId → Bool := fun _ => true) : RcM FVarIdSet := do
  if let some info := (← read).derivedValMap.get? fvarId then
    info.children.foldM (init := s) fun s child =>
      let s := if shouldAdd child then s.insert child else s
      addDescendants child s shouldAdd
  else
    return s

@[specialize]
def useVar (fvarId : FVarId) (shouldBorrow : FVarId → Bool := fun _ => true) : RcM Unit := do
  if !(← isLive fvarId) then
    let liveVars := (← get).liveVars
    let borrows ← addDescendants fvarId liveVars.borrows fun y =>
      !liveVars.vars.contains y && shouldBorrow y
    modify fun s => { s with liveVars := { s.liveVars with borrows := borrows }}
  modify fun s => { s with liveVars := { s.liveVars with vars := s.liveVars.vars.insert fvarId }}

@[inline]
def useArg (args : Array (Arg .impure)) (arg : Arg .impure) : RcM Unit :=
  match arg with
  | .fvar fvarId =>
    useVar fvarId fun y =>
      args.all fun arg =>
        match arg with
        | .fvar z => y != z
        | .erased => true
  | .erased => return ()

def useArgs (args : Array (Arg .impure)) : RcM Unit := do
  args.forM (useArg args)

def useLetValue (value : LetValue .impure) : RcM Unit := do
  match value with
  | .oproj (var := fvarId) .. | .uproj (var := fvarId) .. | .sproj (var := fvarId) ..
  | .box (fvarId := fvarId) .. | .unbox (fvarId := fvarId) .. | .reset (var := fvarId) .. =>
    useVar fvarId
  | .ctor (args := args) .. | .fap (args := args) .. | .pap (args := args) .. =>
    useArgs args
  | .fvar fvarId args .. | .reuse (var := fvarId) (args := args) .. =>
    useVar fvarId
    useArgs args
  | .lit .. | .erased => return ()

@[inline]
def bindVar (fvarId : FVarId) : RcM Unit :=
  modify fun s => { s with liveVars := s.liveVars.erase fvarId }

def setRetLiveVars : RcM Unit := do
  let borrows ← (← read).borrowedParams.foldM (init := {}) fun borrows x =>
    addDescendants x (borrows.insert x)
  set { liveVars := { vars := {}, borrows } : State }

@[inline]
def addInc (fvarId : FVarId) (k : Code .impure) (n : Nat := 1) : RcM (Code .impure) := do
  if n == 0 then
    return k
  else
    let info ← getVarInfo fvarId
    return .inc fvarId n (!info.isDefiniteRef) info.persistent k

@[inline]
def addDec (fvarId : FVarId) (k : Code .impure) : RcM (Code .impure) := do
  let info ← getVarInfo fvarId
  return .dec fvarId 1 (!info.isDefiniteRef) info.persistent k

def addPrologForAlt (altLiveVars : LiveVars) (k : Code .impure) : RcM (Code .impure) := do
  let mut incs := #[]
  let mut decs := #[]
  for fvarId in (← get).liveVars.vars do
    let info ← getVarInfo fvarId
    if !altLiveVars.vars.contains fvarId then
      if info.isPossibleRef && !(← isBorrowed fvarId) then
        decs := decs.push (fvarId, info.idx)
    else if (← isBorrowed fvarId) && !altLiveVars.borrows.contains fvarId then
      incs := incs.push (fvarId, info.idx)

  decs := decs.qsort (fun (_, i₁) (_, i₂) => i₁ < i₂)
  let k ← decs.foldlM (init := k) fun k (v, _) => addDec v k
  incs := incs.qsort (fun (_, i₁) (_, i₂) => i₁ < i₂)
  let k ← incs.foldlM (init := k) fun k (v, _) => addInc v k
  return k

/-- `isFirstOcc xs x i = true` if `xs[i]` is the first occurrence of `xs[i]` in `xs` -/
def isFirstOcc (xs : Array (Arg .impure)) (i : Nat) : Bool :=
  let x := xs[i]!
  i.all fun j _ => xs[j]! != x

/--
Return true if `x` also occurs in `ys` in a position that is not consumed.
That is, it is also passed as a borrow reference.
-/
def isBorrowParamAux (x : FVarId) (ys : Array (Arg .impure)) (consumeParamPred : Nat → Bool) :
    Bool :=
  ys.size.any fun i _ =>
    let y := ys[i]
    match y with
    | .erased => false
    | .fvar y  => x == y && !consumeParamPred i

def isBorrowParam (x : FVarId) (ys : Array (Arg .impure)) (ps : Array (Param .impure)) : Bool :=
  isBorrowParamAux x ys fun i => ! ps[i]!.borrow

/--
Return `n`, the number of times `arg` is consumed.
- `args` is a sequence of instruction parameters where we search for `arg`.
- `consumeParamPred i = true` if parameter `i` is consumed.
-/
def getNumConsumptions (arg : FVarId) (args : Array (Arg .impure)) (consumeParamPred : Nat → Bool) :
    Nat := Id.run do
  let mut num := 0
  for h : i in 0...args.size do
    let arg' := args[i]
    if let .fvar arg' := arg' then
      if arg == arg' && consumeParamPred i then
        num := num + 1
  return num

def addIncBeforeAux (args : Array (Arg .impure)) (consumeParamPred : Nat → Bool)
    (k : Code .impure) : RcM (Code .impure) := do
  let mut k := k
  for h : i in 0...args.size do
    let arg := args[i]
    if let .fvar fvarId := arg then
      let info ← getVarInfo fvarId
      if !info.isPossibleRef || !isFirstOcc args i then
        continue
      let numConsumptions := getNumConsumptions fvarId args consumeParamPred
      let numIncs ←
        if (← isLive fvarId)
            || (← isBorrowed fvarId)
            || isBorrowParamAux fvarId args consumeParamPred then -- `fvarId` is used in a position that is passed as a borrow reference
          pure (numConsumptions)
        else
          pure (numConsumptions - 1)
      k ← addInc fvarId k numIncs
  return k

def addIncBefore (args : Array (Arg .impure)) (ps : Array (Param .impure)) (k : Code .impure) :
    RcM (Code .impure) :=
  addIncBeforeAux args (fun i => !ps[i]!.borrow) k

def addIncBeforeConsumeAll (args : Array (Arg .impure)) (k : Code .impure) :
    RcM (Code .impure) := do
  addIncBeforeAux args (fun _ => true) k

def addDecAfterFullApp (args : Array (Arg .impure)) (ps : Array (Param .impure)) (k : Code .impure) :
    RcM (Code .impure) := do
  let mut k := k
  for h : i in 0...args.size do
    match args[i] with
    | .erased => pure ()
    | .fvar fvarId =>
      /-
      We must add a `dec` if `fvarId` must be consumed, it is alive after the application,
      and it has been borrowed by the application.
      Remark: `fvarId` may occur multiple times in the application (e.g., `f fvarId y fvarId`).
      This is why we check whether it is the first occurrence.
      -/
      let info ← getVarInfo fvarId
      if info.isPossibleRef
          && isFirstOcc args i
          && isBorrowParam fvarId args ps
          && !(← isLive fvarId)
          && !(← isBorrowed fvarId) then
        k ← addDec fvarId k
  return k

/--
Add `dec` for `fvarId` if `fvarId` is a reference, not alive in `k` and not borrowed.
-/
def addDecIfNeeded (fvarId : FVarId) (k : Code .impure) : RcM (Code .impure) := do
  let info ← getVarInfo fvarId
  if info.isPossibleRef && !(← isBorrowed fvarId) && !(← isLive fvarId) then
    addDec fvarId k
  else
    return k

/--
Add `dec` instructions for parameters that are references, are not alive in `k`, and are not borrow.
That is, we must make sure these parameters are consumed.
-/
def addDecForDeadParams (ps : Array (Param .impure)) (k : Code .impure) : RcM (Code .impure) :=
  ps.foldlM (init := k) fun k p => do
    let k ← addDecIfNeeded p.fvarId k
    bindVar p.fvarId
    return k

def LetDecl.explicitRc (code : Code .impure) (decl : LetDecl .impure) (k : Code .impure) :
    RcM (Code .impure) := do
  /-
  `decl.fvarId` can be unused in `k` so we might have to drop it. Note that we do not remove the let
  because we are in the impure phase of the compiler so `decl.value` can have side effects that we
  don't want to loose.
  -/
  let k ← addDecIfNeeded decl.fvarId k
  let k ←
    match decl.value with
    | .ctor (args := args) .. | .reuse (args := args) .. | .pap (args := args) .. =>
      addIncBeforeConsumeAll args (code.updateLet! decl k)
    | .oproj (var := fvarId) .. =>
      let k ← addDecIfNeeded fvarId k
      let k ← if ← isBorrowed decl.fvarId then pure k else addInc decl.fvarId k
      pure <| code.updateLet! decl k
    | .uproj (var := fvarId) .. | .sproj (var := fvarId) .. | .unbox (fvarId := fvarId) .. =>
      let k ← addDecIfNeeded fvarId k
      pure <| code.updateLet! decl k
    | .fap f args =>
      let ps := (← getDeclSig f).get!.params
      let k ← addDecAfterFullApp args ps k
      let liveVars := (← get).liveVars
      let value ←
        if f == ``Array.getInternal && (← isBorrowed decl.fvarId) then
          pure <| .fap ``Array.getInternalBorrowed args
        else if f == ``Array.get!Internal && (← isBorrowed decl.fvarId) then
          pure <| .fap ``Array.get!InternalBorrowed args
        else
          pure <| decl.value
      let decl ← decl.updateValue value
      let k := code.updateLet! decl k
      addIncBefore args ps k
    | .fvar fvarId args =>
      let allArgs := args.push <| .fvar fvarId
      addIncBeforeConsumeAll allArgs (code.updateLet! decl k)
    | .lit .. | .box .. | .reset .. | .erased .. =>
      pure <| code.updateLet! decl k
  useLetValue decl.value
  bindVar decl.fvarId
  return k

partial def Code.explicitRc (code : Code .impure) : RcM (Code .impure) := do
  match code with
  | .let decl k =>
    withLetDecl decl do
      let k ← k.explicitRc
      let k ← decl.explicitRc code k
      return k
  | .jp decl k =>
    let (decl, jpLive) ←
      withParams decl.params do
      withCollectLiveVars do
        let value ← decl.value.explicitRc
        let value ← addDecForDeadParams decl.params value
        decl.updateValue value
    withReader (fun ctx => { ctx with jpLiveVarMap := ctx.jpLiveVarMap.insert decl.fvarId jpLive }) do
      let k ← k.explicitRc
      return code.updateFun! decl k
  | .cases cs =>
    let alts ← cs.alts.mapM fun alt =>
      withCollectLiveVars do
        match alt with
        | .ctorAlt c k =>
          withCtorAlt cs.discr c do
            let k ← k.explicitRc
            return alt.updateCode k
        | .default k =>
          let k ← k.explicitRc
          return alt.updateCode k
    let caseLiveVars := alts.foldl (init := {}) fun acc ⟨_, altLive⟩ => acc.merge altLive
    setLiveVars caseLiveVars
    useVar cs.discr
    let alts ← alts.mapM fun ⟨alt, altLiveVars⟩ => do
      match alt with
      | .ctorAlt c k =>
        withCtorAlt cs.discr c do
          let k ← addPrologForAlt altLiveVars k
          return alt.updateCode k
      | .default k =>
        let k ← addPrologForAlt altLiveVars k
        return alt.updateCode k
    return code.updateAlts! alts
  | .jmp fvarId args =>
    let jpLiveVars ← getJpLiveVars fvarId
    let ps := (← findFunDecl? fvarId).get!.params
    setLiveVars jpLiveVars
    let code ← addIncBefore args ps code
    useArgs args
    return code
  | .return fvarId =>
    setRetLiveVars
    let info ← getVarInfo fvarId
    useVar fvarId
    if info.isPossibleRef && (← isBorrowed fvarId) then
      addInc fvarId code
    else
      return code
  | .uset (var := var) (k := k) .. | .sset (var := var) (k := k) .. =>
    let k ← k.explicitRc
    -- We don't need to insert `y` since we only need to track live variables that are references at runtime
    useVar var
    return code.updateCont! k
  | .unreach .. =>
    setRetLiveVars
    return code
  | .inc .. | .dec .. => unreachable!

def Decl.explicitRc (decl : Decl .impure) (decls : Array (Decl .impure)) :
    CompilerM (Decl .impure) := do
  let value ← decl.value.mapCodeM fun code => do
    let ⟨derivedValMap, borrowedParams⟩ ← CollectDerivedValInfo.collect decl.params code
    go code |>.run {
      borrowedParams,
      derivedValMap,
      decls,
    } |>.run' {}
  return { decl with value }
where
  go (code : Code .impure) : RcM (Code .impure) := do
    withParams decl.params do
      let code ← code.explicitRc
      addDecForDeadParams decl.params code

def run (decls : Array (Decl .impure)) : CompilerM (Array (Decl .impure)) := do
  decls.mapM (·.explicitRc decls)

public def explicitRc : Pass where
  phase := .impure
  phaseOut := .impure
  name := `explicitRc
  run := run

builtin_initialize
  registerTraceClass `Compiler.explicitRc (inherited := true)

end Lean.Compiler.LCNF
