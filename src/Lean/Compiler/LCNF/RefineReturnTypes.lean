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

/-!
This pass refines the return types of impure LCNF functions. After `explicitBoxing`, function return
types may still be `tobject` (the imprecise "tagged or object" type) even when the function body
always returns a `tagged` value or always returns an `object` value. This pass performs a data flow
analysis over function bodies to compute the most precise return type and updates the declarations
accordingly. Running this before `explicitRc` allows the RC insertion pass to skip the
"is this a tagged pointer?" runtime branch in cases where we can statically determine the answer.

The analysis handles mutually recursive SCCs through fixed-point iteration.
-/

namespace Lean.Compiler.LCNF

open ImpureType

/--
Join two impure return type estimates. `none` represents ⊥ (unreachable / no information yet).

The lattice for non-scalar obj types is:
```
     tobject
    /       \
 tagged   object
    \       /
       ⊥ (none)
```
-/
def joinImpureType (a b : Option Expr) : Option Expr :=
  match a, b with
  | none, x | x, none => x
  | some a, some b =>
    if a == b then
      some a
    else if a == tobject || b == tobject then
      some tobject
    else if a.isObj && b.isObj && !a.isScalar && !b.isScalar then
      some tobject
    else
      some a -- scalar types shouldn't mismatch in well-typed IR; keep current

namespace RefineReturnTypes

structure Ctx where
  /-- The SCC declarations we are analyzing. -/
  decls : Array (Decl .impure)
  localTypes : FVarIdMap (Option Expr) := {}

structure State where
  /-- Current return type estimate for each function in the SCC (indexed by position).
      `none` represents ⊥ (unreachable / no information yet). -/
  funTypes : Array (Option Expr)
  /-- Whether any estimate changed in the current iteration. -/
  modified : Bool := false

abbrev RefinM := ReaderT Ctx <| StateRefT State CompilerM

/-- Look up the current type estimate for a function in the SCC by name. -/
def getFunTypeEstimate? (declName : Name) : RefinM (Option (Option Expr)) := do
  let decls := (← read).decls
  match decls.findIdx? (·.name == declName) with
  | some idx => return some (← get).funTypes[idx]!
  | none => return none

@[inline]
def withLocalType (fvarId : FVarId) (type : Option Expr) (x : RefinM α) : RefinM α :=
  withReader (fun ctx => { ctx with localTypes := ctx.localTypes.insert fvarId type }) do
    x

@[inline]
def withParams (ps : Array (Param .impure)) (x : RefinM α) : RefinM α :=
  withReader (fun ctx => { ctx with localTypes := ps.foldl (init := ctx.localTypes) (fun acc p => acc.insert p.fvarId p.type)})
    x

/--
Infer the return type of a code block. Returns `none` for ⊥ (all paths unreachable).

We track a local map from FVarId to callee name for `fap` let-bindings in the SCC,
so that when we hit `.return fvarId` we can use the current fixed-point estimate
instead of the (possibly imprecise) LCtx type.
-/
partial def inferReturnType (code : Code .impure) : RefinM (Option Expr) := do
  match code with
  | .return fvarId | .jmp fvarId _ => return (← read).localTypes.get! fvarId
  | .unreach _ => return none
  | .cases cs =>
    let mut result : Option Expr := none
    for alt in cs.alts do
      let altType ← inferReturnType alt.getCode
      result := joinImpureType result altType
    return result
  | .jp decl k =>
    let jpType ← withParams decl.params do
      inferReturnType decl.value
    withLocalType decl.fvarId jpType do
      inferReturnType k
  | .let decl k =>
    let type ←
      match decl.value with
      | .fap f _ =>
        if let some estimate ← getFunTypeEstimate? f then
          pure estimate
        else
          pure decl.type
      | _ => pure decl.type
    withLocalType decl.fvarId type do
      inferReturnType k
  | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => inferReturnType k
  | .fun .. | .inc .. | .dec .. => unreachable!

def analyzeStep : RefinM Unit := do
  let decls := (← read).decls
  for h : idx in 0...decls.size do
    let decl := decls[idx]
    unless decl.type == tobject do continue
    match decl.value with
    | .code code =>
      let newType ← withParams decl.params do
        inferReturnType code
      let oldType := (← get).funTypes[idx]!
      unless newType == oldType do
        modify fun s => { s with
          funTypes := s.funTypes.set! idx newType
          modified := true
        }
    | .extern .. => pure ()

/-- Run the fixed-point analysis until convergence. -/
partial def analyzeFixpoint (n : Nat := 0) : RefinM Unit := do
  modify fun s => { s with modified := false }
  analyzeStep
  if (← get).modified then
    if n > 10 then
      throwError "Ahhh"
    analyzeFixpoint (n + 1)

/-- Run the analysis and return the refined types for each declaration in the SCC. -/
def runAnalysis (decls : Array (Decl .impure)) : CompilerM (Array Expr) := do
  let initialTypes := decls.map fun decl =>
    if decl.type == tobject then none else some decl.type
  let ctx : Ctx := { decls }
  let state : State := { funTypes := initialTypes }
  let (_, state) ← analyzeFixpoint |>.run ctx |>.run state
  return state.funTypes.zip decls |>.map fun
    | (some ty, _) => ty
    | (none, decl) => decl.type

/--
Update type annotations in a code block to reflect a new return type.
Updates: cases result types, JP types, unreach types.
-/
partial def updateCode (code : Code .impure) (decls : Array (Decl .impure)) (result : Std.HashMap Name Expr) (newType : Expr) : CompilerM (Code .impure) := do
  match code with
  | .let decl k =>
    let k ← updateCode k decls result newType
    match decl.value with
    | .fap f _ =>
      match result[f]? with
      | some type =>
        let decl ← decl.update type decl.value
        return code.updateLet! decl k
      | none => return code.updateCont! k
    | _ => return code.updateCont! k
  | .cases cs =>
    let alts ← cs.alts.mapMonoM (·.mapCodeM (updateCode · decls result newType))
    return code.updateCases! newType cs.discr alts
  | .jp decl k =>
    let value ← updateCode decl.value decls result newType
    let decl ← decl.update newType decl.params value
    let k ← updateCode k decls result newType
    return code.updateFun! decl k
  | .uset (k := k) .. | .sset (k := k) .. =>
    return code.updateCont! (← updateCode k decls result newType)
  | .unreach _ => return code.updateUnreach! newType
  | .return _ | .jmp _ _ => return code
  | .fun .. | .inc .. | .dec .. => unreachable!

end RefineReturnTypes

open RefineReturnTypes in
def refineReturnTypesRun (decls : Array (Decl .impure)) : CompilerM (Array (Decl .impure)) := do
  -- Quick check: if no function returns tobject, nothing to do
  unless decls.any (fun d => d.type == tobject) do return decls
  let refinedTypes ← runAnalysis decls
  let refinedTypesMap := Std.HashMap.ofArray <| decls.map (·.name) |>.zip refinedTypes
  decls.mapIdxM fun i decl => do
    let newType := refinedTypes[i]!
    if newType == decl.type then return decl
    trace[Compiler.refineReturnTypes] "{decl.name}: {decl.type} → {newType}"
    match decl.value with
    | .code code =>
      let code ← updateCode code decls refinedTypesMap newType
      return { decl with type := newType, value := .code code }
    | .extern .. => return { decl with type := newType }

public def refineReturnTypes : Pass where
  phase := .impure
  phaseOut := .impure
  name := `refineReturnTypes
  run := refineReturnTypesRun

builtin_initialize
  registerTraceClass `Compiler.refineReturnTypes (inherited := true)

end Lean.Compiler.LCNF
