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
import Lean.Compiler.LCNF.MonadScope
import Lean.Compiler.LCNF.FVarUtil
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.PrettyPrinter
import Std.Data.Iterators.Producers.Monadic.Array
import Std.Data.Iterators.Combinators.Monadic.Zip

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

Furthermore, the performance related heuristics will be ignored if there is a user-defined
borrow annotation. This allows the user to override the ABI of their function in exchange for
potentially worse code in the function that is being analyzed. Doing so can benefit other functions
that call the current one and thus reduce overall RC pressure.
-/

namespace Lean.Compiler.LCNF

open ImpureType

namespace ParamMap

inductive Key where
  | decl (name : Name)
  | jp (name : Name) (jpId : FVarId)
  deriving BEq, Hashable

end ParamMap

structure ParamMap where
  map : Std.HashMap ParamMap.Key (Array (Param .impure)) := {}
  /--
  The set of fvars that were already annotated as borrowed before arriving at this pass. We try to
  preserve the annotations here if possible.
  -/
  annotatedBorrows : Std.HashSet FVarId := {}

namespace ParamMap

@[inline]
def insert (pm : ParamMap) (k : Key) (ps : Array (Param .impure)) : ParamMap :=
  { pm with map := pm.map.insert k ps }

@[inline]
def erase (pm : ParamMap) (k : Key) : ParamMap :=
  { pm with map := pm.map.erase k }

end ParamMap

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
        modify fun m =>
          { m with
            map := m.map.insert (.decl decl.name) (initParamsIfNotExported exported decl.params),
            annotatedBorrows := decl.params.foldl (init := m.annotatedBorrows) fun acc p =>
              if p.borrow then acc.insert p.fvarId else acc
          }
        goCode decl.name code
      | .extern .. => return ()

  initParams (ps : Array (Param .impure)) : Array (Param .impure) :=
    ps.map fun p => { p with borrow := p.type.isPossibleRef }

  initParamsIfNotExported (exported : Bool) (ps : Array (Param .impure)) : Array (Param .impure) :=
    if exported then
      ps.map ({ · with borrow := false })
    else
      initParams ps

  goCode (declName : Name) (code : Code .impure) : InitM Unit := do
    match code with
    | .jp decl k =>
      modify fun m =>
        { m with
          map := m.map.insert (.jp declName decl.fvarId) (initParams decl.params),
          annotatedBorrows := decl.params.foldl (init := m.annotatedBorrows) fun acc p =>
            if p.borrow then acc.insert p.fvarId else acc
        }
      goCode declName decl.value
      goCode declName k
    | .cases cs => cs.alts.forM (·.forCodeM (goCode declName))
    | .let _ k | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => goCode declName k
    | .return .. | .jmp .. | .unreach .. => return ()
    | .inc .. | .dec .. | .setTag .. | .del .. | .oset .. => unreachable!

/--
Apply the inferred borrow annotations from `map` to a SCC.
-/
partial def apply (decls : Array (Decl .impure)) (map : ParamMap) : CompilerM (Array (Decl .impure)) :=
  decls.mapM fun decl => do
    match decl.value with
    | .code code =>
      let code ← go decl.name code
      let newParams ← updateParams decl.params map.map[ParamMap.Key.decl decl.name]!
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
      let ps ← updateParams decl.params map.map[ParamMap.Key.jp declName decl.fvarId]!
      let decl ← decl.update decl.type ps (← go declName decl.value)
      return code.updateFun! decl (← go declName k)
    | .cases cs => return code.updateAlts! <| ← cs.alts.mapMonoM (·.mapCodeM (go declName))
    | .let _ k | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => return code.updateCont! (← go declName k)
    | .return .. | .jmp .. | .unreach .. => return code
    | .inc .. | .dec .. | .setTag .. | .oset .. | .del .. => unreachable!

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
Reasons why a variable is marked as owned during borrow inference.
-/
inductive OwnReason where
  /-- Target or source of a reset/reuse operation. -/
  | resetReuse (resultFVar : FVarId)
  /-- Result of a constructor allocation. -/
  | constructorResult (resultFVar : FVarId)
  /-- Parameter packed into a constructor. -/
  | constructorArg (resultFVar : FVarId)
  /-- Forward ownership propagation through `oproj`. -/
  | forwardProjectionProp (resultFVar : FVarId)
  /-- Backward ownership propagation through `oproj`. -/
  | backwardProjectionProp (resultFVar : FVarId)
  /-- Result of a function application. -/
  | functionCallResult (resultFVar : FVarId)
  /-- Argument to a function whose corresponding parameter is owned. -/
  | functionCallArg (resultFVar : FVarId)
  /-- Argument or callee in a call to a free variable. -/
  | fvarCall (resultFVar : FVarId)
  /-- Argument in a partial application. -/
  | partialApplication (resultFVar : FVarId)
  /-- Tail call preservation for a self-recursive function call. -/
  | tailCallPreservation (funcName : Name)
  /-- Argument propagation at a join point jump. -/
  | jpArgPropagation (jpFVar : FVarId)
  /-- Tail call preservation at a join point jump. -/
  | jpTailCallPreservation (jpFVar : FVarId)
  /-- Annotated as an owned parameter (currently only triggerable through `@[export]`)-/
  | ownedAnnotation

def OwnReason.toString (reason : OwnReason) : CompilerM String := do
  PP.run do
    match reason with
    | .resetReuse resultFVar => return s!"used in reset reuse {← PP.ppFVar resultFVar}"
    | .constructorResult resultFVar => return s!"result of ctor call {← PP.ppFVar resultFVar}"
    | .constructorArg resultFVar => return s!"argument to constructor call {← PP.ppFVar resultFVar}"
    | .forwardProjectionProp resultFVar => return s!"fwd projection propagation {← PP.ppFVar resultFVar}"
    | .backwardProjectionProp resultFVar => return s!"bkwd projection propagation {← PP.ppFVar resultFVar}"
    | .functionCallResult resultFVar => return s!"result of function call {← PP.ppFVar resultFVar}"
    | .functionCallArg resultFVar => return s!"owned function argument {← PP.ppFVar resultFVar}"
    | .fvarCall resultFVar => return s!"argument to closure call {← PP.ppFVar resultFVar}"
    | .partialApplication resultFVar => return s!"argument to pap {← PP.ppFVar resultFVar}"
    | .tailCallPreservation funcName => return s!"tail call preservation of {funcName}"
    | .jpArgPropagation jpFVar => return s!"backward propagation from JP {← PP.ppFVar jpFVar}"
    | .jpTailCallPreservation jpFVar => return s!"JP tail call preservation {← PP.ppFVar jpFVar}"
    | .ownedAnnotation => return s!"Annotated as owned"

/--
Determine whether an `OwnReason` is necessary for correctness (forced) or just an optimization
(not-forced). If we attempt to own a variable that has been previously annotated as borrow for a
non-forced reason we ignore it.
-/
def OwnReason.isForced (reason : OwnReason) : Bool :=
  match reason with
  -- All of these reasons propagate through ABI decisions and can thus safely be ignored as they
  -- will be accounted for by the reference counting pass.
  | .constructorArg .. | .functionCallArg .. | .fvarCall .. | .partialApplication ..
  | .jpArgPropagation ..
  -- forward propagation can never affect a user-annotated parameter
  | .forwardProjectionProp ..
  -- backward propagation on a user-annotated parameter is only necessary if the projected value
  -- directly flows into a reset-reuse. However, the borrow annotation propagator ensures this
  -- situation never arises
  | .backwardProjectionProp .. => false
  -- Results of functions and constructors are naturally owned.
  | .constructorResult .. | .functionCallResult ..
  -- We cannot pass borrowed values to reset or have borrow annotations destroy tail calls for
  -- correctness reasons.
  | .resetReuse .. | .tailCallPreservation .. | .jpTailCallPreservation ..
  | .ownedAnnotation => true

/--
Infer the borrowing annotations in a SCC through dataflow analysis.
-/
partial def infer (decls : Array (Decl .impure)) : CompilerM ParamMap := do
  let (_, map) ← go |>.run { decls } |>.run { paramMap := ← mkInitParamMap decls }
  return map.paramMap
where
  go : InferM Unit := do
    for (_, params) in (← get).paramMap.map do
      for param in params do
        if !param.borrow && param.type.isPossibleRef then
          -- if the param already disqualifies as borrow now this is because of an annotation
          ownFVar param.fvarId .ownedAnnotation
    modify fun s => { s with modified := false }
    loop

  loop : InferM Unit := do
    step
    if (← get).modified then
      modify fun s => { s with modified := false }
      loop
    else
      return ()

  step : InferM Unit := do
    (← read).decls.forM collectDecl

  ownFVar (fvarId : FVarId) (reason : OwnReason) : InferM Unit := do
    unless (← get).owned.contains fvarId do
      if !reason.isForced && (← get).paramMap.annotatedBorrows.contains fvarId then
        trace[Compiler.inferBorrow] "user annotation blocked owning {← PP.run <| PP.ppFVar fvarId}: {← reason.toString}"
      else
        trace[Compiler.inferBorrow] "own {← PP.run <| PP.ppFVar fvarId}: {← reason.toString}"
        modify fun s => { s with owned := s.owned.insert fvarId, modified := true }

  ownArg (reason : OwnReason) (a : Arg .impure) : InferM Unit := do
    a.forFVarM (ownFVar · reason)

  ownArgs (reason : OwnReason) (as : Array (Arg .impure)) : InferM Unit :=
    as.forM (ownArg reason)

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
    if let some ps := (← get).paramMap.map[k]? then
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
    match (← get).paramMap.map[k]? with
    | some ps => return ps
    | none =>
      let .decl fn := k | unreachable!
      let some sig ← getImpureSignature? fn | throwError "Failed to find LCNF signature for {fn}"
      return sig.params

  /-- For each ps[i], if ps[i] is owned, then mark args[i] as owned. -/
  ownArgsUsingParams (args : Array (Arg .impure)) (ps : Array (Param .impure))
      (reason : OwnReason) : InferM Unit := do
    for h : i in 0...args.size do
      let arg := args[i]
      let p := ps[i]!
      unless p.borrow || p.type.isScalar do ownArg reason arg

  /-- For each args[i], if args[i] is owned, then mark ps[i] as owned.
     We use this action to preserve tail calls. That is, if we have
     a tail call `f xs`, if the i-th parameter is borrowed, but `args[i]` is owned
     we would have to insert a `dec args[i]` after `f args` and consequently
     "break" the tail call. -/
  ownParamsUsingArgs (args : Array (Arg .impure)) (ps : Array (Param .impure))
      (reason : OwnReason) : InferM Unit :=
    for h : i in 0...args.size do
      let arg := args[i]
      let p := ps[i]!
      if let .fvar x := arg then
        if (← isOwned x) then ownFVar p.fvarId reason


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
  ownArgsIfParam (z : FVarId) (args : Array (Arg .impure)) : InferM Unit := do
    for arg in args do
      if let .fvar x := arg then
        if (← read).paramSet.contains x then
          ownFVar x (.constructorArg z)

  collectLetValue (z : FVarId) (v : LetValue .impure) : InferM Unit := do
    match v with
    | .reset _ x => ownFVar z (.resetReuse z); ownFVar x (.resetReuse z)
    | .reuse x _ _ args => ownFVar z (.resetReuse z); ownFVar x (.resetReuse z); ownArgsIfParam z args
    | .oproj _ x _ =>
      if ← isOwned x then ownFVar z (.forwardProjectionProp z)
      if ← isOwned z then ownFVar x (.backwardProjectionProp z)
    -- Keep in sync with ExplicitRC, PropagateBorrow
    | .fap ``Array.getInternal args =>
      if let .fvar parent := args[1]! then
        if ← isOwned parent then ownFVar z (.forwardProjectionProp z)
    | .fap ``Array.get!Internal args =>
      if let .fvar parent := args[1]! then
        if ← isOwned parent then ownFVar z (.forwardProjectionProp z)
      if let .fvar parent := args[2]! then
        if ← isOwned parent then ownFVar z (.forwardProjectionProp z)
    | .fap ``Array.uget args =>
      if let .fvar parent := args[1]! then
        if ← isOwned parent then ownFVar z (.forwardProjectionProp z)
    | .fap f args =>
      -- Constants remain alive at least until the end of execution and can thus effectively be seen
      -- as a "borrowed" read.
      if args.size > 0 then
        let ps ← getParamInfo (.decl f)
        ownFVar z (.functionCallResult z)
        ownArgsUsingParams args ps (.functionCallArg z)
    | .ctor i args =>
      if !i.isScalar then
        ownFVar z (.constructorResult z); ownArgsIfParam z args
    | .fvar x args =>
      ownFVar z (.functionCallResult z); ownFVar x (.fvarCall z); ownArgs (.fvarCall z) args
    | .pap _ args => ownFVar z (.functionCallResult z); ownArgs (.partialApplication z) args
    | _ => return ()

  preserveTailCall (x : FVarId) (v : LetValue .impure) (k : Code .impure) : InferM Unit := do
    match v, k with
    | .fap f args, .return ret =>
      -- NOTE: we currently support TCO for self-calls only, once we do mutual TCO this needs to be
      -- expanded
      if (← read).currDecl == f && x == ret then
        let ps ← getParamInfo (.decl f)
        ownParamsUsingArgs args ps (.tailCallPreservation f)
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
      ownArgsUsingParams args ps (.jpArgPropagation jpId)
      ownParamsUsingArgs args ps (.jpTailCallPreservation jpId)
    | .cases cs => cs.alts.forM (·.forCodeM collectCode)
    | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => collectCode k
    | .return .. | .unreach .. => return ()
    | .inc .. | .dec .. | .setTag .. | .oset .. | .del .. => unreachable!


public def inferBorrow : Pass where
  phase := .impure
  phaseOut := .impure
  name := `inferBorrow
  run decls := do
    let map ← infer decls
    let decls ← apply decls map
    decls.forM (·.saveImpure)
    return decls

builtin_initialize
  registerTraceClass `Compiler.inferBorrow (inherited := true)

end Lean.Compiler.LCNF
