/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager
import Init.While

/-!
This pass expands pairs of reset-reuse instructions into explicit hot and cold paths. We do this on
the LCNF level rather than letting the backend do it because we can apply domain specific
optimizations at this point in time.

Whenever we encounter a `let token := reset nfields orig; k`, we create code of the shape (not
showing reference counting instructions):
```
jp resetjp token isShared :=
  k
cases isShared orig with
  | false -> jmp resetjp orig true
  | true -> jmp resetjp box(0) false
```
Then within the join point body `k` we turn `dec` instructions on `token` into `del` and expand
`let final := reuse token arg; k'` into another join point:
```
jp reusejp final :=
  k'
cases isShared with
  | false -> jmp reusejp token
  | true ->
    let x := alloc args
    jmp reusejp x
```

In addition to this we perform optimizations specific to the hot path for both the `resetjp` and
`reusejp`. For the former, we will frequently encounter the pattern:
```
let x_0 = proj[0] orig
inc x_0
...
let x_i = proj[i] orig
inc x_i
let token := reset nfields orig
```
On the hot path we do not free `orig`, thus there is no need to increment the reference counts of
the projections because the reference coming from `orig` will keep all of the projections alive
naturally (a form of "dynamic derived borrows" if you wish). On the cold path the reference counts
still have to happen though.

For `resetjp` we frequently encounter the pattern:
```
let final := reuse token args
set final[0] := x0
...
set final[i] := xi
```
On the hot path we know that `token` and `orig` refer to the same value. Thus, if we can detect that
one of the `xi` is of the shape `let xi := proj[i] orig`, we can omit the store on the hot path.
Just like with `reusejp` on the cold path we have to perform all the stores.
-/

namespace Lean.Compiler.LCNF

open ImpureType

abbrev Mask := Array (Option FVarId)

/--
Try to erase `inc` instructions on projections of `targetId` occurring in the tail of `ds`.
Return the updated `ds` and mask containing the `FVarId`s whose `inc` was removed.
-/
partial def eraseProjIncFor (nFields : Nat) (targetId : FVarId) (ds : Array (CodeDecl .impure)) :
    CompilerM (Array (CodeDecl .impure) × Mask) := do
  let mut ds := ds
  let mut keep := #[]
  let mut mask := Array.replicate nFields none
  while ds.size ≥ 2 do
    let d := ds.back!
    match d with
    | .let { value := .sproj .., .. } | .let { value := .uproj .., .. } =>
      ds := ds.pop
      keep := keep.push d
    | .inc z n c p =>
      assert! n > 0 -- 0 incs should not be happening
      let d' := ds[ds.size - 2]!
      let .let { fvarId := w, value := .oproj i x _, .. } := d'
        | break
      if !(w == z && targetId == x) then
        break
      if mask[i]!.isSome then
        /-
        Suppose we encounter a situation like
        ```
        let x.1 := proj[0] y
        inc x.1
        let x.2 := proj[0] y
        inc x.2
        ```
        The `inc x.2` will already have been removed. If we don't perform this check we will also
        remove `inc x.1` and have effectively removed two refcounts while only one was legal.
        -/
        keep := keep.push d
        keep := keep.push d'
        ds := ds.pop.pop
        continue
      /-
      Found
      ```
      let z := proj[i] targetId
      inc z n c
      ```
      We keep `proj`, and `inc` when `n > 1`
      -/
      ds := ds.pop.pop
      mask := mask.set! i (some z)
      keep := keep.push d'
      keep := if n == 1 then keep else keep.push (.inc z (n - 1) c p)
    | _ => break

  return (ds ++ keep.reverse, mask)

def mkIf (discr : FVarId) (discrType : Expr) (resultType : Expr) (t e : Code .impure) :
    CompilerM (Code .impure) := do
  return .cases <| .mk discrType.getAppFn.constName! resultType discr #[
    .ctorAlt { name := ``Bool.false, cidx := 0, size := 0, usize := 0, ssize := 0 } e,
    .ctorAlt { name := ``Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0 } t,
  ]

def remapSets (targetId : FVarId) (sets : Array (CodeDecl .impure)) :
    CompilerM (Array (CodeDecl .impure)) :=
  return sets.map fun
    | .oset fvarId i y => .oset targetId i y
    | .sset fvarId i offset y ty => .sset targetId i offset y ty
    | .uset fvarId i y => .uset targetId i y
    | _ => unreachable!

def isSelfOset (fvarId : FVarId) (i : Nat) (y : Arg .impure) : CompilerM Bool := do
  match y with
  | .fvar y =>
    let some value ← findLetValue? (pu := .impure) y | return false
    let .oproj i' fvarId' := value | return false
    return i == i' && fvarId == fvarId'
  | .erased => return false

def isSelfUset (fvarId : FVarId) (i : Nat) (y : FVarId) : CompilerM Bool := do
  let some value ← findLetValue? (pu := .impure) y | return false
  let .uproj i' fvarId' := value | return false
  return i == i' && fvarId == fvarId'

def isSelfSset (fvarId : FVarId) (i : Nat) (offset : Nat) (y : FVarId) :
    CompilerM Bool := do
  let some value ← findLetValue? (pu := .impure) y | return false
  let .sproj i' offset' fvarId' := value | return false
  return i == i' && offset == offset' && fvarId == fvarId'

/--
Partition the set instructions in `sets` into a pair `(selfSets, necessarySets)` where `selfSets`
contain instructions that perform a set with the same value projected from `selfId` and
`necessarySets` all others.
-/
def partitionSelfSets (selfId : FVarId) (sets : Array (CodeDecl .impure)) :
    CompilerM (Array (CodeDecl .impure) × Array (CodeDecl .impure)) := do
  let mut necessarySets := #[]
  let mut selfSets := #[]
  for set in sets do
    let isSelfSet :=
      match set with
      | .oset _ i y => isSelfOset selfId i y
      | .uset _ i y => isSelfUset selfId i y
      | .sset _ i offset y _ => isSelfSset selfId i offset y
      | _ => unreachable!
    if ← isSelfSet then
      selfSets := selfSets.push set
    else
      necessarySets := necessarySets.push set

  return (selfSets, necessarySets)

def collectSucceedingSets (target : FVarId) (k : Code .impure) :
    CompilerM (Array (CodeDecl .impure) × Code .impure) := do
  let mut sets := #[]
  let mut k := k
  while true do
    match k with
    | .oset (fvarId := fvarId) (k := k') .. | .sset (fvarId := fvarId) (k := k') ..
    | .uset (fvarId := fvarId) (k := k') .. =>
      if target != fvarId then
        break
      sets := sets.push k.toCodeDecl!
      k := k'
    | _ => break
  return (sets, k)

mutual

/--
Expand the matching `reuse`/`dec` for the allocation in `origAllocId` whose `reset` token is in
`resetTokenId`.
-/
partial def processResetCont (resetTokenId : FVarId) (code : Code .impure) (origAllocId : FVarId)
    (isSharedId : FVarId) (currentRetType : Expr) : CompilerM (Code .impure) := do
  match code with
  | .dec y n _ _ k =>
    if resetTokenId == y then
      assert! n == 1 -- n must be one since `resetToken := reset ...`
      return .del resetTokenId k
    else
      let k ← processResetCont resetTokenId k origAllocId isSharedId currentRetType
      return code.updateCont! k
  | .let decl k =>
    match decl.value with
    | .reuse y c u xs =>
      if resetTokenId != y then
        let k ← processResetCont resetTokenId k origAllocId isSharedId currentRetType
        return code.updateCont! k

      let (succeedingSets, k) ← collectSucceedingSets decl.fvarId k
      let (selfSets, necessarySets) ← partitionSelfSets origAllocId succeedingSets
      let k := attachCodeDecls necessarySets k

      let param := {
        fvarId := decl.fvarId,
        binderName := decl.binderName,
        type := decl.type,
        borrow := false
      }
      let contJp ← mkFunDecl (← mkFreshBinderName `reusejp) currentRetType #[param] k

      let slowPath ← mkSlowPath decl c xs contJp.fvarId selfSets
      let fastPath ← mkFastPath resetTokenId c u xs contJp.fvarId origAllocId

      eraseLetDecl decl

      let reuse ← mkIf isSharedId uint8 currentRetType slowPath fastPath
      return .jp contJp reuse
    | _ =>
      let k ← processResetCont resetTokenId k origAllocId isSharedId currentRetType
      return code.updateCont! k
  | .cases cs =>
    return code.updateAlts! (← cs.alts.mapMonoM (·.mapCodeM (processResetCont resetTokenId · origAllocId isSharedId cs.resultType)))
  | .jp decl k =>
    let decl ← decl.updateValue (← processResetCont resetTokenId decl.value origAllocId isSharedId decl.type)
    let k ← processResetCont resetTokenId k origAllocId isSharedId currentRetType
    return code.updateFun! decl k
  | .uset (k := k) .. | .sset (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
  | .del (k := k) .. | .oset (k := k) .. =>
    let k ← processResetCont resetTokenId k origAllocId isSharedId currentRetType
    return code.updateCont! k
  | .jmp .. | .return .. | .unreach .. => return code
where
  /--
  On the slow path we have to:
  1. Make a fresh alloation
  2. Apply all the self sets as the fresh allocation is of course not in sync with the original one.
  3. Pass the fresh allocation to the joinpoint.
  -/
  mkSlowPath (decl : LetDecl .impure) (info : CtorInfo) (args : Array (Arg .impure))
      (contJpId : FVarId) (selfSets : Array (CodeDecl .impure)) : CompilerM (Code .impure) := do
    let allocDecl ← mkLetDecl (← mkFreshBinderName `reuseFailAlloc) decl.type (.ctor info args)
    let mut code := .jmp contJpId #[.fvar allocDecl.fvarId]
    code := attachCodeDecls (← remapSets allocDecl.fvarId selfSets) code
    code := .let allocDecl code
    return code

  /--
  On the fast path path we have to:
  1. Make all non-self object sets to "simulate" the allocation (the remaining necessary sets will
     be made in the continuation)
  2. Pass the reused allocation to the joinpoint.
  -/
  mkFastPath (resetTokenId : FVarId) (info : CtorInfo) (update : Bool) (args : Array (Arg .impure))
      (contJpId : FVarId) (origAllocId : FVarId) : CompilerM (Code .impure) := do
    let mut code := .jmp contJpId #[.fvar resetTokenId]
    for h : idx in 0...args.size do
      if !(← isSelfOset origAllocId idx args[idx]) then
        code := .oset resetTokenId idx args[idx] code
    if update then
      code := .setTag resetTokenId info.cidx code
    return code

/--
Traverse `code` looking for reset-reuse pairs to expand while `ds` holds the instructions up to the
last branching point.
-/
partial def Code.expandResetReuse (code : Code .impure) (ds : Array (CodeDecl .impure))
    (currentRetType : Expr) : CompilerM (Code .impure) := do
  let collectAndGo (code : Code .impure) (ds : Array (CodeDecl .impure)) (k : Code .impure) :=
    let d := code.toCodeDecl!
    k.expandResetReuse (ds.push d) currentRetType
  match code with
  | .let decl k =>
    match decl.value with
    | .reset nFields origAllocId => expand ds decl nFields origAllocId k
    | _ => collectAndGo code ds k
  | .jp decl k =>
    let value ← decl.value.expandResetReuse #[] decl.type
    let decl ← decl.updateValue value
    k.expandResetReuse (ds.push (.jp decl)) currentRetType
  | .cases cs =>
    let alts ← cs.alts.mapMonoM (·.mapCodeM (·.expandResetReuse #[] cs.resultType))
    let code := code.updateAlts! alts
    return attachCodeDecls ds code
  | .uset (k := k) .. | .sset (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
  | .dec (k := k) .. | .del (k := k) .. | .oset (k := k) .. =>
    collectAndGo code ds k
  | .jmp .. | .return .. | .unreach .. =>
    return attachCodeDecls ds code
where
  /--
  Expand the reset in `decl` together with its matching `reuse`/`dec`s in its continuation `k`.
  -/
  expand (ds : Array (CodeDecl .impure)) (decl : LetDecl .impure) (nFields : Nat)
      (origAllocId : FVarId) (k : Code .impure) : CompilerM (Code .impure) := do
    let (ds, mask) ← eraseProjIncFor nFields origAllocId ds
    let isSharedParam ← mkParam (← mkFreshBinderName `isShared) uint8 false
    let k ← processResetCont decl.fvarId k origAllocId isSharedParam.fvarId currentRetType
    let k ← k.expandResetReuse #[] currentRetType
    let allocParam := {
      fvarId := decl.fvarId,
      binderName := decl.binderName,
      type := tobject,
      borrow := false
    }
    let resetJp ← mkFunDecl (← mkFreshBinderName `resetjp) currentRetType #[allocParam, isSharedParam] k
    let isSharedDecl ← mkLetDecl (← mkFreshBinderName `isSharedCheck) uint8 (.isShared origAllocId)
    let slowPath ← mkSlowPath origAllocId mask resetJp.fvarId isSharedDecl.fvarId
    let fastPath ← mkFastPath origAllocId mask resetJp.fvarId isSharedDecl.fvarId
    let mut reset ← mkIf isSharedDecl.fvarId uint8 currentRetType slowPath fastPath
    reset := .let isSharedDecl reset
    eraseLetDecl decl
    return attachCodeDecls ds (.jp resetJp reset)

  /--
  On the slow path we cannot reuse the allocation, this means we have to:
  1. Increments all variables projected from `origAllocId` that have not been incremented yet by
     the shared prologue. On the fast path they are kept alive naturally by the original allocation
     but here that is not necessarily the case.
  2. Decrement the value being reset (the natural behavior of a failed reset)
  3. Pass box(0) as a reuse value into the continuation join point
  -/
  mkSlowPath (origAllocId : FVarId) (mask : Mask) (resetJpId : FVarId) (isSharedId : FVarId) :
      CompilerM (Code .impure) := do
    let mut code := .jmp resetJpId #[.erased, .fvar isSharedId]
    code := .dec origAllocId 1 true false code
    for fvarId? in mask do
      let some fvarId := fvarId? | continue
      code := .inc fvarId 1 true false code
    return code

  /--
  On the fast path we can reuse the allocation, this means we have to:
  1. decrement all unread fields as their parent allocation would usually be dropped at this point
     and we want to be garbage free.
  2. Pass the original allocation as a reuse value into the continuation join point
  -/
  mkFastPath (origAllocId : FVarId) (mask : Mask) (resetJpId : FVarId) (isSharedId : FVarId) :
      CompilerM (Code .impure) := do
    let mut code := .jmp resetJpId #[.fvar origAllocId, .fvar isSharedId]
    for h : idx in 0...mask.size do
      if mask[idx].isSome then
        continue
      let fieldDecl ← mkLetDecl (← mkFreshBinderName `unused) tobject (.oproj idx origAllocId)
      code := .let fieldDecl (.dec fieldDecl.fvarId 1 true false code)
    return code

end

def Decl.expandResetReuse (decl : Decl .impure) : CompilerM (Decl .impure) := do
  if (← getConfig).resetReuse then
    let value ← decl.value.mapCodeM (·.expandResetReuse #[] decl.type)
    let decl := { decl with value }
    return decl
  else
    return decl

public def expandResetReuse : Pass :=
  Pass.mkPerDeclaration `expandResetReuse .impure Decl.expandResetReuse

builtin_initialize
  registerTraceClass `Compiler.expandResetReuse (inherited := true)

end Lean.Compiler.LCNF
