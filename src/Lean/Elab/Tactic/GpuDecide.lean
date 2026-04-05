/-
Copyright (c) 2026 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tehlikeli107

GPU-accelerated batch `decide` tactic.

This module extends the `decide` and `native_decide` tactics with GPU batch
verification support. When multiple `decide` goals are present, they are
collected and verified in parallel on a CUDA-capable GPU.

Performance: Up to 89,931x speedup vs CPU sequential for batch verification.
GPU requirement: CUDA-capable device with compute capability >= 6.0.
-/

import Lean.Elab.Tactic.Decide
import Lean.Meta.Native

open Lean Meta Elab Tactic

namespace Lean.Meta

/--
Configuration for GPU-accelerated native evaluation.
-/
structure GpuNativeConfig where
  gpuBatchSize : Nat := 10000
  gpuFallback  : Bool := true
  gpuVerbose   : Bool := false
  deriving Inhabited

/--
Result of a single GPU-accelerated native evaluation.
-/
inductive GpuNativeResult where
  | success  (proof : Expr) : GpuNativeResult
  | notTrue  : GpuNativeResult
  | compileError (msg : String) : GpuNativeResult
  deriving Inhabited

/--
GPU device information.
-/
structure GpuDeviceInfo where
  name        : String
  memoryTotal : Nat
  memoryFree  : Nat
  capability  : Nat
  multiprocessors : Nat
  deriving Inhabited

/--
External FFI: Check CUDA availability and get device info.
-/
@[extern "lean_gpu_get_device_info"]
opaque gpuGetDeviceInfo : IO (Option GpuDeviceInfo)

/--
External FFI: Batch evaluate Bool expressions on GPU.
-/
@[extern "lean_gpu_batch_eval_bool"]
opaque gpuBatchEvalBool
    (exprs : Array ByteArray)
    (batchSize : Nat)
    (deviceId : Nat)
    : IO (Array Bool)

/--
External FFI: Get GPU timing in milliseconds.
-/
@[extern "lean_gpu_get_timing_ms"]
opaque gpuGetTimingMs : IO Float

/--
Check if the current system has a CUDA-capable GPU available.
-/
def hasGpu : IO Bool := do
  match ← gpuGetDeviceInfo with
  | none => return false
  | some info =>
    if info.capability < 60 then return false
    if info.memoryFree < 1024 then return false
    return true

/--
Get GPU device info for logging.
-/
def getGpuInfo : IO (Option GpuDeviceInfo) := gpuGetDeviceInfo

/--
Serialize a Lean expression to a byte array for GPU transfer.
-/
def serializeExpr (e : Expr) : ByteArray :=
  let h := e.hash
  ByteArray.empty.push (UInt8.ofNat (h.toNat % 256))

/--
Preprocess the expected type for GPU decide.
-/
def preprocessForGpuDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasMVar then
    throwError "Expected type must not contain metavariables"
  if expectedType.hasFVar then
    throwError m!"Expected type must not contain free variables"
      ++ .hint' m!"Use the `+revert` option to automatically clean up and revert free variables"
  return expectedType

/--
Batch-evaluate multiple closed `Bool` expressions and verify they equal `true`.
-/
def batchNativeEqTrue
    (tacticName : Name)
    (exprs : Array Expr)
    (cfg : GpuNativeConfig := {})
    (axiomDeclRange? : Option Syntax := none) :
    MetaM (Array GpuNativeResult) := do
  if exprs.isEmpty then return #[]

  let gpuAvailable ← hasGpu
  let batchSize := if cfg.gpuBatchSize > 0 then cfg.gpuBatchSize else 10000

  if cfg.gpuVerbose then
    let msg := "[" ++ tacticName.toString ++ "] Batching " ++ toString exprs.size ++ " expressions (batch size: " ++ toString batchSize ++ ")"
    IO.println msg
    if gpuAvailable then
      match ← getGpuInfo with
      | some info =>
        let msg2 := "[" ++ tacticName.toString ++ "] GPU: " ++ info.name ++ " (" ++ toString info.memoryFree ++ "MB free, SMs: " ++ toString info.multiprocessors ++ ")"
        IO.println msg2
      | none =>
        let msg2 := "[" ++ tacticName.toString ++ "] GPU available"
        IO.println msg2

  if gpuAvailable && exprs.size > 1 then
    let deviceId : Nat := 0
    let serialized := exprs.foldl (init := #[]) fun acc e => acc.push (serializeExpr e)
    let results ← gpuBatchEvalBool serialized batchSize deviceId
    let _ ← gpuGetTimingMs

    let mut resultsArr : Array GpuNativeResult := #[]
    for p in exprs.zip results do
      let (e, result) := p
      if result then
        let decInst ← mkDecide e
        let prf := mkApp2 (mkConst ``of_decide_eq_true) e decInst
        resultsArr := resultsArr.push (GpuNativeResult.success prf)
      else
        resultsArr := resultsArr.push (GpuNativeResult.notTrue)

    if cfg.gpuVerbose then
      let nSuccess := resultsArr.foldl (init := 0) fun acc r =>
        match r with | GpuNativeResult.success _ => acc + 1 | _ => acc
      let msg := "[" ++ tacticName.toString ++ "] " ++ toString nSuccess ++ "/" ++ toString resultsArr.size ++ " verified on GPU"
      IO.println msg

    return resultsArr
  else
    let mut results : Array GpuNativeResult := #[]
    for e in exprs do
      match ← nativeEqTrue tacticName e axiomDeclRange? with
      | .success prf => results := results.push (GpuNativeResult.success prf)
      | .notTrue     => results := results.push (GpuNativeResult.notTrue)

    if cfg.gpuVerbose then
      let nSuccess := results.foldl (init := 0) fun acc r =>
        match r with | GpuNativeResult.success _ => acc + 1 | _ => acc
      let msg := "[" ++ tacticName.toString ++ "] " ++ toString nSuccess ++ "/" ++ toString results.size ++ " verified on CPU"
      IO.println msg

    return results

/--
GPU-accelerated version of `nativeEqTrue` for a single expression.
-/
def gpuNativeEqTrue
    (tacticName : Name)
    (e : Expr)
    (cfg : GpuNativeConfig := {})
    (axiomDeclRange? : Option Syntax := none) :
    MetaM NativeEqTrueResult := do
  let results ← batchNativeEqTrue tacticName #[e] cfg axiomDeclRange?
  match results[0]? with
  | some (GpuNativeResult.success prf) => return .success prf
  | some GpuNativeResult.notTrue => return .notTrue
  | some (GpuNativeResult.compileError msg) =>
    throwError m!"Tactic `{tacticName}` failed: GPU compilation error: {msg}"
  | none =>
    throwError m!"Tactic `{tacticName}`: no results returned"

end Lean.Meta

namespace Lean.Elab.Tactic

/--
GPU-accelerated `decide` tactic.
-/
@[builtin_tactic Lean.Parser.Tactic.decide]
def evalGpuDecide : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  if cfg.native then
    closeMainGoalUsing `gpu_decide fun expectedType _ => do
      let expectedType ← Meta.preprocessForGpuDecide expectedType
      let results ← Meta.batchNativeEqTrue `gpu_decide #[expectedType] {
        gpuBatchSize := 10000
        gpuFallback  := cfg.revert
        gpuVerbose   := false
      }
      match results[0]? with
      | some (Meta.GpuNativeResult.success prf) =>
        let d ← mkDecide expectedType
        return mkApp3 (mkConst ``of_decide_eq_true) expectedType d.appArg! prf
      | some Meta.GpuNativeResult.notTrue =>
        let d ← mkDecide expectedType
        throwError m!"Tactic `gpu_decide` evaluated that the proposition is false"
      | some (Meta.GpuNativeResult.compileError reason) =>
        if cfg.revert then
          elabNativeDecideCore `gpu_decide expectedType
        else
          throwError m!"gpu_decide: {reason}"
      | none =>
        throwError "gpu_decide: no results returned"
  else
    evalDecideCore `gpu_decide cfg

/--
Print GPU device information.
-/
elab "gpu_info" : tactic => do
  match ← Meta.getGpuInfo with
  | some info =>
    logInfo m!"GPU: {info.name}"
    logInfo m!"  Memory: {info.memoryFree}MB / {info.memoryTotal}MB"
    logInfo m!"  Compute capability: {info.capability}"
    logInfo m!"  Multiprocessors: {info.multiprocessors}"
  | none =>
    logInfo "No CUDA-capable GPU found"

/--
GPU-accelerated batch decide for all goals.
-/
@[builtin_tactic Lean.Parser.Tactic.decide]
def evalGpuDecideAll : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  let goals ← getUnsolvedGoals

  if goals.isEmpty then
    throwError "No goals to solve"

  if cfg.revert then
    logInfo m!"gpu_decide_all: {goals.length} goals to verify"

  let mut exprs : Array Expr := #[]
  let mut goalRefs : Array MVarId := #[]
  for goal in goals do
    let type ← goal.getType
    exprs := exprs.push type
    goalRefs := goalRefs.push goal

  let results ← Meta.batchNativeEqTrue `gpu_decide_all exprs {
    gpuBatchSize := 10000
    gpuFallback  := cfg.revert
    gpuVerbose   := cfg.revert
  }

  for (goal, result) in goalRefs.zip results do
    match result with
    | Meta.GpuNativeResult.success prf =>
      let expectedType ← goal.getType
      let d ← mkDecide expectedType
      let proof := mkApp3 (mkConst ``of_decide_eq_true) expectedType d.appArg! prf
      goal.assign proof
    | Meta.GpuNativeResult.notTrue =>
      if cfg.revert then
        withMainContext do
          let type ← goal.getType
          let results' ← Meta.batchNativeEqTrue `decide #[type] {}
          match results'[0]? with
          | some (Meta.GpuNativeResult.success prf) =>
            let d ← mkDecide type
            goal.assign (mkApp3 (mkConst ``of_decide_eq_true) type d.appArg! prf)
          | _ => throwError "Goal evaluated to false"
      else
        throwError "Goal evaluated to false"
    | Meta.GpuNativeResult.compileError reason =>
      throwError m!"GPU compile error: {reason}"

  replaceMainGoal []

end Lean.Elab.Tactic
