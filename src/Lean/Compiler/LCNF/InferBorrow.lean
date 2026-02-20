/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.ExportAttr
import Std.Data.Iterators.Producers.Array
import Std.Data.Iterators.Combinators.Zip
import Lean.Compiler.LCNF.MonadScope
import Lean.Compiler.LCNF.FVarUtil
import Lean.Compiler.LCNF.PhaseExt

/-!
This pass is responsible for inferring borrow annotations to the parameters of functions and join
points. When a parameter is marked as borrowed, the caller can be sure that the function will not
decrement the reference count of the parameter. Thus, if the value is still used after the call, the
caller does not need to `inc` it before calling in order to ensure that it stays alive.

The inference is done with a data flow analysis which initially assumes all arguments are passed as
borrowed and subsequently refines this by marking parameters as owned as required and propagating
the information throughout the program. The analysis has two reasons for marking a parameter as owned.
Some parameters need to be owned for correctness, while others are heuristically marked as owned to
reduce reference counting pressure inside of the function.

The correctness ones are the following:
- We preserve tail calls to recursive functions and join points by ensuring we never have to insert
  a `dec` after a tail call. This is done by marking parameters of tail-called functions/jps as owned
  if a respective argument at a call site is owned.
- We ensure that values which are subject to reset-reuse are owned so their reference count
  accurately reflects the real amount of references.

For performance we:
- propagate through annotations of functions that we call. That is if we call another function `f`
  which has an owned parameter we ensure that the argument we are passing is owned as well. In
  particular when `f` is partially applied we ensure that all arguments are owned.
- When passing a parameter into a constructor we ensure it is passed as owned so we do not have
  to `inc` before calling the constructor.
-/

namespace Lean.Compiler.LCNF

open ImpureType

namespace ParamMap

inductive Key where
  | decl (name : Name)
  | jp (name : Name) (jpId : FVarId)
  deriving BEq, Hashable

end ParamMap

abbrev ParamMap := Std.HashMap ParamMap.Key (Array (Param .impure))

/-- Mark parameters that take a reference as borrow -/
def initBorrow (ps : Array (Param .impure)) : Array (Param .impure) :=
  ps.map fun p => { p with borrow := p.type.isPossibleRef }

abbrev InitM := StateRefT ParamMap CompilerM

partial def mkInitParamMap (decls : Array (Decl .impure)) : CompilerM ParamMap := do
  let (_, map) ← go decls |>.run {}
  return map
where
  go (decls : Array (Decl .impure)) : InitM Unit :=
    decls.forM fun decl => do
      match decl.value with
      | .code code =>
        let exported := isExport (← getEnv) decl.name
        modify fun m => m.insert (.decl decl.name) (initParamsIfNotExported exported decl.params)
        goCode decl.name code
      | .extern .. => return ()

  initParams (ps : Array (Param .impure)) : Array (Param .impure) :=
    ps.map fun p => { p with borrow := p.type.isPossibleRef }

  initParamsIfNotExported (exported : Bool) (ps : Array (Param .impure)) : Array (Param .impure) :=
    if exported then ps else initParams ps

  goCode (declName : Name) (code : Code .impure) : InitM Unit := do
    match code with
    | .jp decl k =>
      modify fun m => m.insert (.jp declName decl.fvarId) (initParams decl.params)
      goCode declName decl.value
      goCode declName k
    | .cases cs => cs.alts.forM (·.forCodeM (goCode declName))
    | .let _ k | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => goCode declName k
    | .return .. | .jmp .. | .unreach .. => return ()
    | .inc .. | .dec .. => unreachable!

/--
Apply the inferred borrow annotations from `map` to a SCC.
-/
partial def apply (decls : Array (Decl .impure)) (map : ParamMap) : CompilerM (Array (Decl .impure)) :=
  decls.mapM fun decl => do
    match decl.value with
    | .code code =>
      let code ← go decl.name code
      let newParams ← updateParams decl.params map[ParamMap.Key.decl decl.name]!
      return { decl with value := .code code, params := newParams }
    | _ => return decl
where
  updateParams (ps : Array (Param .impure)) (borrows : Array (Param .impure)) :
      CompilerM (Array (Param .impure)) := do
    ps.iterM (m := CompilerM)
      |>.zip (borrows.iterM _)
      |>.mapM (fun (p, b) => p.updateBorrow b.borrow)
      |>.toArray

  go (declName : Name) (code : Code .impure) : CompilerM (Code .impure) := do
    match code with
    | .jp decl k =>
      let ps ← updateParams decl.params map[ParamMap.Key.jp declName decl.fvarId]!
      let decl ← decl.update decl.type ps (← go declName decl.value)
      return code.updateFun! decl (← go declName k)
    | .cases cs => return code.updateAlts! <| ← cs.alts.mapMonoM (·.mapCodeM (go declName))
    | .let _ k | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => return code.updateCont! (← go declName k)
    | .return .. | .jmp .. | .unreach .. => return code
    | .inc .. | .dec .. => unreachable!

structure Ctx where
  /--
  The SCC we are analyzing.
  -/
  decls : Array (Decl .impure)
  /--
  The declaration that we are currently working inside of.
  -/
  currDecl : Name := default
  /--
  The set of all function parameters in scope. This is used to implement the heuristic at
  `ownArgsUsingParams`.
  -/
  paramSet : FVarIdSet := {}

structure State where
  /--
  Set of variables that must be owned.
  -/
  owned : FVarIdHashSet := {}
  modified : Bool := false
  paramMap : ParamMap

abbrev InferM := ReaderT Ctx <| StateRefT State CompilerM

instance : MonadScope InferM where
  getScope := return (← read).paramSet
  withScope f mx := withReader (fun ctx => { ctx with paramSet := f ctx.paramSet }) mx

/--
Infer the borrowing annotations in a SCC through dataflow analysis.
-/
partial def infer (decls : Array (Decl .impure)) : CompilerM ParamMap := do
  let (_, map) ← go |>.run { decls } |>.run { paramMap := ← mkInitParamMap decls }
  return map.paramMap
where
  go : InferM Unit := do
    step
    if (← get).modified then
      modify fun s => { s with modified := false }
      go
    else
      return ()

  step : InferM Unit := do
    (← read).decls.forM collectDecl

  ownFVar (fvarId : FVarId) : InferM Unit := do
    modify fun s =>
      if s.owned.contains fvarId then
        s
      else
        { s with owned := s.owned.insert fvarId, modified := true }

  ownArg (a : Arg .impure) : InferM Unit := do
    a.forFVarM ownFVar

  ownArgs (as : Array (Arg .impure)) : InferM Unit :=
    as.forM ownArg

  isOwned (fvarId : FVarId) : InferM Bool := return (← get).owned.contains fvarId

  collectDecl (decl : Decl .impure) : InferM Unit := do
    match decl.value with
    | .code code =>
      withParams decl.params do
      withReader (fun ctx => { ctx with currDecl := decl.name }) do
        collectCode code
        updateParamMap (.decl decl.name)
    | _ => return ()

  /-- Updates `map[k]` using the current set of `owned` variables. -/
  updateParamMap (k : ParamMap.Key) : InferM Unit := do
    if let some ps := (← get).paramMap[k]? then
      -- This is to ensure linearity over ps in the following code, if you know how to make this
      -- linear in a nice fashion please make a PR
      modify fun s => { s with paramMap := s.paramMap.erase k }
      let ps ← ps.mapM fun p => do
        if !p.borrow then
          return p
        else if ← isOwned p.fvarId then
          modify fun s => { s with modified := true }
          return { p with borrow := false }
        else
          return p
      modify fun s => { s with paramMap := s.paramMap.insert k ps }

  getParamInfo (k : ParamMap.Key) : InferM (Array (Param .impure)) := do
    match (← get).paramMap[k]? with
    | some ps => return ps
    | none =>
      let .decl fn := k | unreachable!
      let some sig ← getImpureSignature? fn | throwError "Failed to find LCNF signature for {fn}"
      return sig.params

  /-- For each ps[i], if ps[i] is owned, then mark args[i] as owned. -/
  ownArgsUsingParams (args : Array (Arg .impure)) (ps : Array (Param .impure)) : InferM Unit := do
    for h : i in 0...args.size do
      let arg := args[i]
      let p := ps[i]!
      unless p.borrow || p.type.isScalar do ownArg arg

  /-- For each args[i], if args[i] is owned, then mark ps[i] as owned.
     We use this action to preserve tail calls. That is, if we have
     a tail call `f xs`, if the i-th parameter is borrowed, but `args[i]` is owned
     we would have to insert a `dec args[i]` after `f args` and consequently
     "break" the tail call. -/
  ownParamsUsingArgs (args : Array (Arg .impure)) (ps : Array (Param .impure)) : InferM Unit :=
    for h : i in 0...args.size do
      let arg := args[i]
      let p := ps[i]!
      if let .fvar x := arg then
        if (← isOwned x) then ownFVar p.fvarId


  /-- Mark `args[i]` as owned if it is one of the parameters that are currently in scope.
     We use this action to mark function parameters that are being "packed" inside constructors.
     This is a heuristic, and is not related with the effectiveness of the reset/reuse optimization.
     It is useful for code such as
     ```
     def f (x y : obj) :=
     let z := ctor_1 x y;
     ret z
     ```
  -/
  ownArgsIfParam (args : Array (Arg .impure)) : InferM Unit := do
    for arg in args do
      if let .fvar x := arg then
        if (← read).paramSet.contains x then
          ownFVar x

  collectLetValue (z : FVarId) (v : LetValue .impure) : InferM Unit := do
    match v with
    | .reset _ x => ownFVar z; ownFVar x
    | .reuse x _ _ args => ownFVar z; ownFVar x; ownArgsIfParam args
    | .ctor _ args => ownFVar z; ownArgsIfParam args
    | .oproj _ x _ =>
      if ← isOwned x then ownFVar z
      if ← isOwned z then ownFVar x
    | .fap f args =>
      let ps ← getParamInfo (.decl f)
      ownFVar z
      ownArgsUsingParams args ps
    | .fvar x args => ownFVar z; ownFVar x; ownArgs args
    | .pap _ args => ownFVar z; ownArgs args
    | _ => return ()

  preserveTailCall (x : FVarId) (v : LetValue .impure) (k : Code .impure) : InferM Unit := do
    match v, k with
    | .fap f args, .return ret =>
      -- NOTE: we currently support TCO for self-calls only, once we do mutual TCO this needs to be
      -- expanded
      if (← read).currDecl == f && x == ret then
        let ps ← getParamInfo (.decl f)
        ownParamsUsingArgs args ps
    | _, _ => return ()

  collectCode (code : Code .impure) : InferM Unit := do
    match code with
    | .jp decl k =>
      withParams decl.params do
        collectCode decl.value
      let ctx ← read
      updateParamMap (.jp ctx.currDecl decl.fvarId)
      collectCode k
    | .let decl k =>
      collectCode k
      collectLetValue decl.fvarId decl.value
      preserveTailCall decl.fvarId decl.value k
    | .jmp jpId args =>
      let ctx ← read
      let ps ← getParamInfo (.jp ctx.currDecl jpId)
      ownArgsUsingParams args ps -- for making sure the join point can reuse
      ownParamsUsingArgs args ps -- for making sure the tail call is preserved
    | .cases cs => cs.alts.forM (·.forCodeM collectCode)
    | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => collectCode k
    | .return .. | .unreach .. => return ()
    | .inc .. | .dec .. => unreachable!


public def inferBorrow : Pass where
  phase := .impure
  phaseOut := .impure
  name := `inferBorrow
  run decls := do
    let map ← infer decls
    apply decls map

builtin_initialize
  registerTraceClass `Compiler.inferBorrow (inherited := true)

end Lean.Compiler.LCNF
