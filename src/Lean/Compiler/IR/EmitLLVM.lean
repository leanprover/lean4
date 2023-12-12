/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

import Lean.Data.HashMap
import Lean.Runtime
import Lean.Compiler.NameMangling
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.Boxing
import Lean.Compiler.IR.ResetReuse
import Lean.Compiler.IR.LLVMBindings

open Lean.IR.ExplicitBoxing (isBoxedName)

namespace Lean.IR

def leanMainFn := "_lean_main"

namespace LLVM
-- TODO(bollu): instantiate target triple and find out what size_t is.
def size_tType (llvmctx : LLVM.Context) : IO (LLVM.LLVMType llvmctx) :=
  LLVM.i64Type llvmctx

-- Helper to add a function if it does not exist, and to return the function handle if it does.
def getOrAddFunction (m : LLVM.Module ctx) (name : String) (type : LLVM.LLVMType ctx) : BaseIO (LLVM.Value ctx) :=  do
  match (← LLVM.getNamedFunction m name) with
  | some fn => return fn
  | none =>
    /-
    By the evidence shown in: https://github.com/leanprover/lean4/issues/2373#issuecomment-1658743284
    this is how clang implements `-fstack-clash-protection` in the LLVM IR, we want this feature
    for robust stack overflow detection.
    -/
    let fn ← LLVM.addFunction m name type
    let attr ← LLVM.createStringAttribute "probe-stack" "inline-asm"
    LLVM.addAttributeAtIndex fn LLVM.AttributeIndex.AttributeFunctionIndex attr
    return fn

def getOrAddGlobal (m : LLVM.Module ctx) (name : String) (type : LLVM.LLVMType ctx) : BaseIO (LLVM.Value ctx) :=  do
  match (← LLVM.getNamedGlobal m name) with
  | .some fn => return fn
  | .none => LLVM.addGlobal m name type

end LLVM

namespace EmitLLVM

structure Context (llvmctx : LLVM.Context) where
  env        : Environment
  modName    : Name
  jpMap      : JPParamsMap := {}
  mainFn     : FunId := default
  mainParams : Array Param := #[]
  llvmmodule : LLVM.Module llvmctx

structure State (llvmctx : LLVM.Context) where
  var2val : HashMap VarId (LLVM.LLVMType llvmctx × LLVM.Value llvmctx)
  jp2bb   : HashMap JoinPointId (LLVM.BasicBlock llvmctx)

abbrev Error := String

abbrev M (llvmctx : LLVM.Context) :=
  StateRefT (State llvmctx) (ReaderT (Context llvmctx) (ExceptT Error IO))

instance : Inhabited (M llvmctx α) where
  default := throw "Error: inhabitant"

def addVartoState (x : VarId) (v : LLVM.Value llvmctx) (ty : LLVM.LLVMType llvmctx) : M llvmctx Unit := do
  modify (fun s => { s with var2val := s.var2val.insert x (ty, v) }) -- add new variable

def addJpTostate (jp : JoinPointId) (bb : LLVM.BasicBlock llvmctx) : M llvmctx Unit :=
  modify (fun s => { s with jp2bb := s.jp2bb.insert jp bb })

def emitJp (jp : JoinPointId) : M llvmctx (LLVM.BasicBlock llvmctx) := do
  let state ← get
  match state.jp2bb.find? jp with
  | .some bb => return bb
  | .none => throw s!"unable to find join point {jp}"

def getLLVMModule : M llvmctx (LLVM.Module llvmctx) := Context.llvmmodule <$> read

def getEnv : M llvmctx Environment := Context.env <$> read

def getModName : M llvmctx  Name := Context.modName <$> read

def getDecl (n : Name) : M llvmctx Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => throw s!"unknown declaration {n}"

def constIntUnsigned (n : Nat) : M llvmctx (LLVM.Value llvmctx) :=  do
    LLVM.constIntUnsigned llvmctx (UInt64.ofNat n)

def getOrCreateFunctionPrototype (mod : LLVM.Module llvmctx)
    (retty : LLVM.LLVMType llvmctx) (name : String) (args : Array (LLVM.LLVMType llvmctx)) : M llvmctx  (LLVM.Value llvmctx) := do
  LLVM.getOrAddFunction mod name $ ← LLVM.functionType retty args (isVarArg := false)

def callLeanBox (builder : LLVM.Builder llvmctx)
    (arg : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_box"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ ← LLVM.size_tType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn  #[arg] name

def callLeanMarkPersistentFn (builder : LLVM.Builder llvmctx) (arg : LLVM.Value llvmctx) : M llvmctx  Unit := do
  let fnName :=  "lean_mark_persistent"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ←   LLVM.buildCall2 builder fnty fn  #[arg]

-- `lean_{inc, dec}_{ref?}_{1,n}`
inductive RefcountKind where
  | inc | dec

instance : ToString RefcountKind where
  toString
    | .inc => "inc"
    | .dec => "dec"

def callLeanRefcountFn (builder : LLVM.Builder llvmctx)
    (kind : RefcountKind) (checkRef? : Bool) (arg : LLVM.Value llvmctx)
    (delta : Option (LLVM.Value llvmctx) := Option.none) : M llvmctx Unit := do
  let fnName :=  s!"lean_{kind}{if checkRef? then "" else "_ref"}{if delta.isNone then "" else "_n"}"
  let retty ← LLVM.voidType llvmctx
  let argtys := if delta.isNone then #[← LLVM.voidPtrType llvmctx] else #[← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  match delta with
  | .none => do
    -- since refcount δ is 1, we only supply the pointer.
    let _ ← LLVM.buildCall2 builder fnty fn #[arg]
  | .some n => do
    let _ ← LLVM.buildCall2 builder fnty fn #[arg, n]

-- `decRef1`
-- Do NOT attempt to merge this code with callLeanRefcountFn, because of the uber confusing
-- semantics of 'ref?'. If 'ref?' is true, it calls the version that is lean_dec
def callLeanDecRef (builder : LLVM.Builder llvmctx) (res : LLVM.Value llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_dec_ref"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.i8PtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[res]

def callLeanUnsignedToNatFn (builder : LLVM.Builder llvmctx)
    (n : Nat) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let mod ← getLLVMModule
  let argtys := #[← LLVM.i32Type llvmctx]
  let retty ← LLVM.voidPtrType llvmctx
  let f ←   getOrCreateFunctionPrototype mod retty "lean_unsigned_to_nat"  argtys
  let fnty ← LLVM.functionType retty argtys
  let nv ← LLVM.constInt32 llvmctx (UInt64.ofNat n)
  LLVM.buildCall2 builder fnty f #[nv] name

def callLeanMkStringFromBytesFn (builder : LLVM.Builder llvmctx)
    (strPtr nBytes : LLVM.Value llvmctx) (name : String) : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_mk_string_from_bytes"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys :=  #[← LLVM.voidPtrType llvmctx, ← LLVM.i64Type llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[strPtr, nBytes] name

def callLeanMkString (builder : LLVM.Builder llvmctx)
    (strPtr : LLVM.Value llvmctx) (name : String) : M llvmctx (LLVM.Value llvmctx) := do
  let retty ← LLVM.voidPtrType llvmctx
  let argtys :=  #[← LLVM.voidPtrType llvmctx]
  let fn ←  getOrCreateFunctionPrototype (← getLLVMModule) retty "lean_mk_string" argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[strPtr] name

def callLeanCStrToNatFn (builder : LLVM.Builder llvmctx)
    (n : Nat) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_cstr_to_nat"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys :=  #[← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let s ← LLVM.buildGlobalString builder (value := toString n)
  LLVM.buildCall2 builder fnty fn #[s] name

def callLeanIOMkWorld (builder : LLVM.Builder llvmctx) : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_mk_world"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys :=  #[]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[] "mk_io_out"

def callLeanIOResultIsError (builder : LLVM.Builder llvmctx)
    (arg : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_result_is_error"
  let retty ← LLVM.i1Type llvmctx
  let argtys :=  #[← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[arg] name

def callLeanAllocCtor (builder : LLVM.Builder llvmctx)
    (tag num_objs scalar_sz : Nat) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_alloc_ctor"
  let retty ← LLVM.voidPtrType llvmctx
  let i32 ← LLVM.i32Type llvmctx
  let argtys :=  #[i32, i32, i32]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys

  let tag ← LLVM.constInt32 llvmctx (UInt64.ofNat tag)
  let num_objs ← LLVM.constInt32 llvmctx (UInt64.ofNat num_objs)
  let scalar_sz ← LLVM.constInt32 llvmctx (UInt64.ofNat scalar_sz)
  LLVM.buildCall2 builder fnty fn #[tag, num_objs, scalar_sz] name

def callLeanCtorSet (builder : LLVM.Builder llvmctx)
    (o i v : LLVM.Value llvmctx) : M llvmctx Unit := do
  let fnName := "lean_ctor_set"
  let retty ← LLVM.voidType llvmctx
  let voidptr ← LLVM.voidPtrType llvmctx
  let unsigned ← LLVM.size_tType llvmctx
  let argtys :=  #[voidptr, unsigned, voidptr]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  _ <- LLVM.buildCall2 builder fnty fn  #[o, i, v]

def callLeanIOResultMKOk (builder : LLVM.Builder llvmctx)
    (v : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_result_mk_ok"
  let voidptr ← LLVM.voidPtrType llvmctx
  let retty := voidptr
  let argtys :=  #[voidptr]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[v] name

def callLeanAllocClosureFn (builder : LLVM.Builder llvmctx)
    (f arity nys : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_alloc_closure"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn  #[f, arity, nys] retName

def callLeanClosureSetFn (builder : LLVM.Builder llvmctx)
    (closure ix arg : LLVM.Value llvmctx) (retName : String := "") : M llvmctx Unit := do
  let fnName :=  "lean_closure_set"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[closure, ix, arg] retName

def callLeanObjTag (builder : LLVM.Builder llvmctx)
    (closure : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_obj_tag"
  let retty ← LLVM.i32Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let out ← LLVM.buildCall2 builder fnty fn  #[closure] retName
  LLVM.buildSextOrTrunc builder out (← LLVM.i64Type llvmctx)

def callLeanIOResultGetValue (builder : LLVM.Builder llvmctx)
    (v : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_result_get_value"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[v] name

def callLeanCtorRelease (builder : LLVM.Builder llvmctx)
    (closure i : LLVM.Value llvmctx) (retName : String := "") : M llvmctx Unit := do
  let fnName :=  "lean_ctor_release"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[closure, i] retName

def callLeanCtorSetTag (builder : LLVM.Builder llvmctx)
    (closure i : LLVM.Value llvmctx) (retName : String := "") : M llvmctx Unit := do
  let fnName :=  "lean_ctor_set_tag"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[closure, i] retName

def toLLVMType (t : IRType) : M llvmctx (LLVM.LLVMType llvmctx) := do
  match t with
  | IRType.float      => LLVM.doubleTypeInContext llvmctx
  | IRType.uint8      => LLVM.intTypeInContext llvmctx 8
  | IRType.uint16     => LLVM.intTypeInContext llvmctx 16
  | IRType.uint32     => LLVM.intTypeInContext llvmctx 32
  | IRType.uint64     => LLVM.intTypeInContext llvmctx 64
  -- TODO: how to cleanly size_t in LLVM? We can do eg. instantiate the current target and query for size.
  | IRType.usize      => LLVM.size_tType llvmctx
  | IRType.object     => do LLVM.pointerType (← LLVM.i8Type llvmctx)
  | IRType.tobject    => do LLVM.pointerType (← LLVM.i8Type llvmctx)
  | IRType.irrelevant => do LLVM.pointerType (← LLVM.i8Type llvmctx)
  | IRType.struct _ _ => panic! "not implemented yet"
  | IRType.union _ _  => panic! "not implemented yet"

def throwInvalidExportName {α : Type} (n : Name) : M llvmctx α := do
  throw s!"invalid export name {n.toString}"

def toCName (n : Name) : M llvmctx String := do
  match getExportNameFor? (← getEnv) n with
  | some (.str .anonymous s) => pure s
  | some _                   => throwInvalidExportName n
  | none                     => if n == `main then pure leanMainFn else pure n.mangle

def toCInitName (n : Name) : M llvmctx String := do
  match getExportNameFor? (← getEnv) n with
  | some (.str .anonymous s) => return "_init_" ++ s
  | some _                   => throwInvalidExportName n
  | none                     => pure ("_init_" ++ n.mangle)

/--
## LLVM Control flow Utilities
-/

-- Indicates whether the API for building the blocks for then/else should
-- forward the control flow to the merge block.
inductive ShouldForwardControlFlow where
| yes | no

-- Get the function we are currently inserting into.
def builderGetInsertionFn (builder : LLVM.Builder llvmctx) : M llvmctx (LLVM.Value llvmctx) := do
  let builderBB ← LLVM.getInsertBlock builder
  LLVM.getBasicBlockParent builderBB

def builderAppendBasicBlock (builder : LLVM.Builder llvmctx) (name : String) : M llvmctx (LLVM.BasicBlock llvmctx) := do
  let fn ← builderGetInsertionFn builder
  LLVM.appendBasicBlockInContext llvmctx fn name

def buildWhile_ (builder : LLVM.Builder llvmctx) (name : String)
    (condcodegen : LLVM.Builder llvmctx → M llvmctx (LLVM.Value llvmctx))
    (bodycodegen : LLVM.Builder llvmctx → M llvmctx Unit) : M llvmctx Unit := do
  let fn ← builderGetInsertionFn builder

  let nameHeader := name ++ "header"
  let nameBody := name ++ "body"
  let nameMerge := name ++ "merge"

  -- cur → header
  let headerbb ← LLVM.appendBasicBlockInContext llvmctx fn nameHeader
  let _ ← LLVM.buildBr builder headerbb

  let bodybb ← LLVM.appendBasicBlockInContext llvmctx fn nameBody
  let mergebb ← LLVM.appendBasicBlockInContext llvmctx fn nameMerge

  -- header → {body, merge}
  LLVM.positionBuilderAtEnd builder headerbb
  let cond ← condcodegen builder
  let _ ← LLVM.buildCondBr builder cond bodybb mergebb

  -- body → header
  LLVM.positionBuilderAtEnd builder bodybb
  bodycodegen builder
  let _ ← LLVM.buildBr builder headerbb

  -- merge
  LLVM.positionBuilderAtEnd builder mergebb

-- build an if, and position the builder at the merge basic block after execution.
-- The '_' denotes that we return Unit on each branch.
def buildIfThen_ (builder : LLVM.Builder llvmctx) (name : String) (brval : LLVM.Value llvmctx)
    (thencodegen : LLVM.Builder llvmctx → M llvmctx ShouldForwardControlFlow) : M llvmctx Unit := do
  let fn ← builderGetInsertionFn builder

  let nameThen := name ++ "Then"
  let nameElse := name ++ "Else"
  let nameMerge := name ++ "Merge"

  let thenbb ← LLVM.appendBasicBlockInContext llvmctx fn nameThen
  let elsebb ← LLVM.appendBasicBlockInContext llvmctx fn nameElse
  let mergebb ← LLVM.appendBasicBlockInContext llvmctx fn nameMerge
  let _ ← LLVM.buildCondBr builder brval thenbb elsebb
  -- then
  LLVM.positionBuilderAtEnd builder thenbb
  let fwd? ← thencodegen builder
  match fwd? with
  | .yes => let _ ← LLVM.buildBr builder mergebb
  | .no => pure ()
  -- else
  LLVM.positionBuilderAtEnd builder elsebb
  let _ ← LLVM.buildBr builder mergebb
  -- merge
  LLVM.positionBuilderAtEnd builder mergebb

def buildIfThenElse_ (builder : LLVM.Builder llvmctx)  (name : String) (brval : LLVM.Value llvmctx)
    (thencodegen : LLVM.Builder llvmctx → M llvmctx ShouldForwardControlFlow)
    (elsecodegen : LLVM.Builder llvmctx → M llvmctx ShouldForwardControlFlow) : M llvmctx Unit := do
  let fn ← LLVM.getBasicBlockParent (← LLVM.getInsertBlock builder)
  let thenbb ← LLVM.appendBasicBlockInContext llvmctx fn (name ++ "Then")
  let elsebb ← LLVM.appendBasicBlockInContext llvmctx fn (name ++ "Else")
  let mergebb ← LLVM.appendBasicBlockInContext llvmctx fn (name ++ "Merge")
  let _ ← LLVM.buildCondBr builder brval thenbb elsebb
  -- then
  LLVM.positionBuilderAtEnd builder thenbb
  let fwd? ← thencodegen builder
  match fwd? with
  | .yes => let _ ← LLVM.buildBr builder mergebb
  | .no => pure ()
  -- else
  LLVM.positionBuilderAtEnd builder elsebb
  let fwd? ← elsecodegen builder
  match fwd? with
  | .yes => let _ ← LLVM.buildBr builder mergebb
  | .no => pure ()
  -- merge
  LLVM.positionBuilderAtEnd builder mergebb

-- Recall that lean uses `i8` for booleans, not `i1`, so we need to compare with `true`.
def buildLeanBoolTrue? (builder : LLVM.Builder llvmctx)
    (b : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  LLVM.buildICmp builder LLVM.IntPredicate.NE b (← LLVM.constInt8 llvmctx 0) name

def emitFnDeclAux (mod : LLVM.Module llvmctx)
    (decl : Decl) (cppBaseName : String) (isExternal : Bool) : M llvmctx (LLVM.Value llvmctx) := do
  let ps := decl.params
  let env ← getEnv
  -- bollu: if we have a declaration with no parameters, then we emit it as a global pointer.
  -- bollu: Otherwise, we emit it as a function
  let global ←
    if ps.isEmpty then
        let retty ← (toLLVMType decl.resultType)
        let global ← LLVM.getOrAddGlobal mod cppBaseName retty
        if !isExternal then
          LLVM.setInitializer global (← LLVM.getUndef retty)
        pure global
    else
        let retty ← (toLLVMType decl.resultType)
        let mut argtys := #[]
        for p in ps do
          -- if it is extern, then we must not add irrelevant args
          if !(isExternC env decl.name) || !p.ty.isIrrelevant then
            argtys := argtys.push (← toLLVMType p.ty)
        -- TODO (bollu): simplify this API, this code of `closureMaxArgs` is duplicated in multiple places.
        if argtys.size > closureMaxArgs && isBoxedName decl.name then
          argtys := #[← LLVM.pointerType (← LLVM.voidPtrType llvmctx)]
        let fnty ← LLVM.functionType retty argtys (isVarArg := false)
        LLVM.getOrAddFunction mod cppBaseName fnty
  -- we must now set symbol visibility for global.
  if ps.isEmpty then
    if isClosedTermName env decl.name then LLVM.setVisibility global LLVM.Visibility.hidden -- static
    else if isExternal then pure () -- extern (Recall that C/LLVM funcs are extern linkage by default.)
    else LLVM.setDLLStorageClass global LLVM.DLLStorageClass.export  -- LEAN_EXPORT
  else if !isExternal
    -- An extern decl might be linked in from a different translation unit.
    -- Thus, we cannot export an external declaration as we do not define it,
    -- only declare its presence.
    -- So, we only export non-external definitions.
    then LLVM.setDLLStorageClass global LLVM.DLLStorageClass.export
  return global


def emitFnDecl (decl : Decl) (isExternal : Bool) : M llvmctx Unit := do
  let cppBaseName ← toCName decl.name
  let _ ← emitFnDeclAux (← getLLVMModule) decl cppBaseName isExternal

def emitExternDeclAux (decl : Decl) (cNameStr : String) : M llvmctx Unit := do
  let env ← getEnv
  let extC := isExternC env decl.name
  let _ ← emitFnDeclAux (← getLLVMModule) decl cNameStr extC

def emitFnDecls : M llvmctx Unit := do
  let env ← getEnv
  let decls := getDecls env
  let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {}
  let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {}
  let usedDecls := usedDecls.toList
  for n in usedDecls do
    let decl ← getDecl n
    match getExternNameFor env `c decl.name with
    | some cName => emitExternDeclAux decl cName
    | none       => emitFnDecl decl (!modDecls.contains n)
  return ()

def emitLhsSlot_ (x : VarId) : M llvmctx (LLVM.LLVMType llvmctx × LLVM.Value llvmctx) := do
  let state ← get
  match state.var2val.find? x with
  | .some v => return v
  | .none => throw s!"unable to find variable {x}"

def emitLhsVal (builder : LLVM.Builder llvmctx)
    (x : VarId) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let (xty, xslot) ← emitLhsSlot_ x
  LLVM.buildLoad2 builder xty xslot name

def emitLhsSlotStore (builder : LLVM.Builder llvmctx)
    (x : VarId) (v : LLVM.Value llvmctx) : M llvmctx Unit := do
  let (_, slot) ← emitLhsSlot_ x
  LLVM.buildStore builder v slot

def emitArgSlot_ (builder : LLVM.Builder llvmctx)
    (x : Arg) : M llvmctx (LLVM.LLVMType llvmctx × LLVM.Value llvmctx) := do
  match x with
  | Arg.var x => emitLhsSlot_ x
  | _ => do
    let slotty ← LLVM.voidPtrType llvmctx
    let slot ← LLVM.buildAlloca builder slotty "irrelevant_slot"
    let v ← callLeanBox builder (← LLVM.constIntUnsigned llvmctx 0) "irrelevant_val"
    let _ ← LLVM.buildStore builder v slot
    return (slotty, slot)

def emitArgVal (builder : LLVM.Builder llvmctx)
    (x : Arg) (name : String := "") : M llvmctx (LLVM.LLVMType llvmctx × LLVM.Value llvmctx) := do
  let (xty, xslot) ← emitArgSlot_ builder x
  let xval ← LLVM.buildLoad2 builder xty xslot name
  return (xty, xval)

def emitAllocCtor (builder : LLVM.Builder llvmctx)
    (c : CtorInfo) : M llvmctx (LLVM.Value llvmctx) := do
  -- TODO(bollu) : find the correct size, don't assume 'void*' size is 8
  let hackSizeofVoidPtr := 8
  let scalarSize := hackSizeofVoidPtr * c.usize + c.ssize
  callLeanAllocCtor builder c.cidx c.size scalarSize "lean_alloc_ctor_out"

def emitCtorSetArgs (builder : LLVM.Builder llvmctx)
    (z : VarId) (ys : Array Arg) : M llvmctx Unit := do
  ys.size.forM fun i => do
    let zv ← emitLhsVal builder z
    let (_yty, yv) ← emitArgVal builder ys[i]!
    let iv ← LLVM.constIntUnsigned llvmctx (UInt64.ofNat i)
    callLeanCtorSet builder zv iv yv
    emitLhsSlotStore builder z zv
    pure ()

def emitCtor (builder : LLVM.Builder llvmctx)
    (z : VarId) (c : CtorInfo) (ys : Array Arg) : M llvmctx Unit := do
  let (_llvmty, slot) ← emitLhsSlot_ z
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    let v ← callLeanBox builder (← constIntUnsigned c.cidx) "lean_box_outv"
    let _ ← LLVM.buildStore builder v slot
  else do
    let v ← emitAllocCtor builder c
    let _ ← LLVM.buildStore builder v slot
    emitCtorSetArgs builder z ys

def emitInc (builder : LLVM.Builder llvmctx)
    (x : VarId) (n : Nat) (checkRef? : Bool) : M llvmctx Unit := do
  let xv ← emitLhsVal builder x
  if n != 1
  then do
     let nv ← LLVM.constIntUnsigned llvmctx (UInt64.ofNat n)
     callLeanRefcountFn builder (kind := RefcountKind.inc) (checkRef? := checkRef?) (delta := nv) xv
  else callLeanRefcountFn builder (kind := RefcountKind.inc) (checkRef? := checkRef?) xv

def emitDec (builder : LLVM.Builder llvmctx)
    (x : VarId) (n : Nat) (checkRef? : Bool) : M llvmctx Unit := do
  let xv ← emitLhsVal builder x
  if n != 1
  then throw "expected n = 1 for emitDec"
  else callLeanRefcountFn builder (kind := RefcountKind.dec) (checkRef? := checkRef?) xv

def emitNumLit (builder : LLVM.Builder llvmctx)
    (t : IRType) (v : Nat) : M llvmctx (LLVM.Value llvmctx) := do
  if t.isObj then
    if v < UInt32.size then
      callLeanUnsignedToNatFn builder v
    else
      callLeanCStrToNatFn builder v
  else
    LLVM.constInt (← toLLVMType t) (UInt64.ofNat v)

def toHexDigit (c : Nat) : String :=
  String.singleton c.digitChar

-- TODO(bollu) : Setup code sharing between 'EmitC' and 'EmitLLVM'
def quoteString (s : String) : String :=
  let q := "\"";
  let q := s.foldl
    (fun q c => q ++
      if c == '\n' then "\\n"
      else if c == '\r' then "\\r"
      else if c == '\t' then "\\t"
      else if c == '\\' then "\\\\"
      else if c == '\"' then "\\\""
      else if c.toNat <= 31 then
        "\\x" ++ toHexDigit (c.toNat / 16) ++ toHexDigit (c.toNat % 16)
      -- TODO(Leo) : we should use `\unnnn` for escaping unicode characters.
      else String.singleton c)
    q;
  q ++ "\""

def emitSimpleExternalCall (builder : LLVM.Builder llvmctx)
    (f : String)
    (ps : Array Param)
    (ys : Array Arg)
    (retty : IRType)
    (name : String) : M llvmctx (LLVM.Value llvmctx) := do
  let mut args := #[]
  let mut argTys := #[]
  for (p, y) in ps.zip ys do
    if !p.ty.isIrrelevant then
      let (_yty, yv) ← emitArgVal builder y ""
      argTys := argTys.push (← toLLVMType p.ty)
      args := args.push yv
  let fnty ← LLVM.functionType (← toLLVMType retty) argTys
  let fn ← LLVM.getOrAddFunction (← getLLVMModule) f fnty
  LLVM.buildCall2 builder fnty fn args name

-- TODO: if the external call is one that we cannot code generate, give up and
-- generate fallback code.
def emitExternCall (builder : LLVM.Builder llvmctx)
    (f : FunId)
    (ps : Array Param)
    (extData : ExternAttrData)
    (ys : Array Arg) (retty : IRType)
    (name : String := "") : M llvmctx (LLVM.Value llvmctx) :=
  match getExternEntryFor extData `c with
  | some (ExternEntry.standard _ extFn) => emitSimpleExternalCall builder extFn ps ys retty name
  | some (ExternEntry.inline "llvm" _pat) => throw "Unimplemented codegen of inline LLVM"
  | some (ExternEntry.inline _ pat) => throw s!"Cannot codegen non-LLVM inline code '{pat}'."
  | some (ExternEntry.foreign _ extFn)  => emitSimpleExternalCall builder extFn ps ys retty name
  | _ => throw s!"Failed to emit extern application '{f}'."

def getFunIdTy (f : FunId) : M llvmctx (LLVM.LLVMType llvmctx) := do
  let decl ← getDecl f
  let retty ← toLLVMType decl.resultType
  let argtys ← decl.params.mapM (fun p => do toLLVMType p.ty)
  LLVM.functionType retty argtys

/--
Create a function declaration and return a pointer to the function.
If the function actually takes arguments, then we must have a function pointer in scope.
If the function takes no arguments, then it is a top-level closed term, and its value will
be stored in a global pointer. So, we load from the global pointer. The type of the global is function pointer pointer.
This returns a *function pointer.*
-/
def getOrAddFunIdValue (builder : LLVM.Builder llvmctx) (f : FunId) : M llvmctx (LLVM.Value llvmctx) := do
  let decl ← getDecl f
  let fcname ← toCName f
  let retty ← toLLVMType decl.resultType
  if decl.params.isEmpty then
     let gslot ← LLVM.getOrAddGlobal (← getLLVMModule) fcname retty
     LLVM.buildLoad2 builder retty gslot
  else
    let argtys ← decl.params.mapM (fun p => do toLLVMType p.ty)
    let fnty ← LLVM.functionType retty argtys
    LLVM.getOrAddFunction (← getLLVMModule) fcname fnty

def emitPartialApp (builder : LLVM.Builder llvmctx) (z : VarId) (f : FunId) (ys : Array Arg) : M llvmctx Unit := do
  let decl ← getDecl f
  let fv ← getOrAddFunIdValue builder f
  let arity := decl.params.size
  let (_zty, zslot) ← emitLhsSlot_ z
  let zval ← callLeanAllocClosureFn builder fv
                                    (← constIntUnsigned arity)
                                    (← constIntUnsigned ys.size)
  LLVM.buildStore builder zval zslot
  ys.size.forM fun i => do
    let (yty, yslot) ← emitArgSlot_ builder ys[i]!
    let yval ← LLVM.buildLoad2 builder yty yslot
    callLeanClosureSetFn builder zval (← constIntUnsigned i) yval

def emitApp (builder : LLVM.Builder llvmctx) (z : VarId) (f : VarId) (ys : Array Arg) : M llvmctx Unit := do
  if ys.size > closureMaxArgs then do
    let aargs ← LLVM.buildAlloca builder (← LLVM.arrayType (← LLVM.voidPtrType llvmctx) (UInt64.ofNat ys.size)) "aargs"
    for i in List.range ys.size do
      let (yty, yv) ← emitArgVal builder ys[i]!
      let aslot ← LLVM.buildInBoundsGEP2 builder yty aargs #[← constIntUnsigned 0, ← constIntUnsigned i] s!"param_{i}_slot"
      LLVM.buildStore builder yv aslot
    let fnName :=  s!"lean_apply_m"
    let retty ← LLVM.voidPtrType llvmctx
    let args := #[← emitLhsVal builder f, ← constIntUnsigned ys.size, aargs]
    -- '1 + ...'. '1' for the fn and 'args' for the arguments
    let argtys := #[← LLVM.voidPtrType llvmctx]
    let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
    let fnty ← LLVM.functionType retty argtys
    let zv ← LLVM.buildCall2 builder fnty fn args
    emitLhsSlotStore builder z zv
  else do

    let fnName :=  s!"lean_apply_{ys.size}"
    let retty ← LLVM.voidPtrType llvmctx
    let args : Array (LLVM.Value llvmctx) := #[← emitLhsVal builder f] ++ (← ys.mapM (fun y => Prod.snd <$> (emitArgVal builder y)))
    -- '1 + ...'. '1' for the fn and 'args' for the arguments
    let argtys := (List.replicate (1 + ys.size) (← LLVM.voidPtrType llvmctx)).toArray
    let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
    let fnty ← LLVM.functionType retty argtys
    let zv ← LLVM.buildCall2 builder fnty fn args
    emitLhsSlotStore builder z zv

def emitFullApp (builder : LLVM.Builder llvmctx)
    (z : VarId) (f : FunId) (ys : Array Arg) : M llvmctx Unit := do
  let (__zty, zslot) ← emitLhsSlot_ z
  let decl ← getDecl f
  match decl with
  | Decl.extern _ ps retty extData =>
     let zv ← emitExternCall builder f ps extData ys retty
     LLVM.buildStore builder zv zslot
  | Decl.fdecl .. =>
    if ys.size > 0 then
        let fv ← getOrAddFunIdValue builder f
        let ys ←  ys.mapM (fun y => do
            let (yty, yslot) ← emitArgSlot_ builder y
            let yv ← LLVM.buildLoad2 builder yty yslot
            return yv)
        let zv ← LLVM.buildCall2 builder (← getFunIdTy f) fv ys
        LLVM.buildStore builder zv zslot
    else
       let zv ← getOrAddFunIdValue builder f
       LLVM.buildStore builder zv zslot

-- Note that this returns a *slot*, just like `emitLhsSlot_`.
def emitLit (builder : LLVM.Builder llvmctx)
    (z : VarId) (t : IRType) (v : LitVal) : M llvmctx (LLVM.Value llvmctx) := do
  let llvmty ← toLLVMType t
  let zslot ← LLVM.buildAlloca builder llvmty
  addVartoState z zslot llvmty
  let zv ← match v with
            | LitVal.num v => emitNumLit builder t v
            | LitVal.str v =>
                 let zero ← LLVM.constIntUnsigned llvmctx 0
                 let str_global ← LLVM.buildGlobalString builder v
                 -- access through the global, into the 0th index of the array
                 let strPtr ← LLVM.buildInBoundsGEP2 builder
                                (← LLVM.opaquePointerTypeInContext llvmctx)
                                str_global #[zero] ""
                 let nbytes ← LLVM.constIntUnsigned llvmctx (UInt64.ofNat (v.utf8ByteSize))
                 callLeanMkStringFromBytesFn builder strPtr nbytes ""
  LLVM.buildStore builder zv zslot
  return zslot

def callLeanCtorGet (builder : LLVM.Builder llvmctx)
    (x i : LLVM.Value llvmctx) (retName : String) : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_ctor_get"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.i32Type llvmctx]
  let fnty ← LLVM.functionType retty argtys
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let i ← LLVM.buildSextOrTrunc builder i (← LLVM.i32Type llvmctx)
  LLVM.buildCall2 builder fnty fn  #[x, i] retName

def emitProj (builder : LLVM.Builder llvmctx) (z : VarId) (i : Nat) (x : VarId) : M llvmctx Unit := do
  let xval ← emitLhsVal builder x
  let zval ← callLeanCtorGet builder xval (← constIntUnsigned i) ""
  emitLhsSlotStore builder z zval

def callLeanCtorGetUsize (builder : LLVM.Builder llvmctx)
    (x i : LLVM.Value llvmctx) (retName : String) : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_ctor_get_usize"
  let retty ← LLVM.size_tType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fnty ← LLVM.functionType retty argtys
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  LLVM.buildCall2 builder fnty fn  #[x, i] retName

def emitUProj (builder : LLVM.Builder llvmctx) (z : VarId) (i : Nat) (x : VarId) : M llvmctx Unit := do
  let xval ← emitLhsVal builder x
  let zval ← callLeanCtorGetUsize builder xval (← constIntUnsigned i) ""
  emitLhsSlotStore builder z zval

def emitOffset (builder : LLVM.Builder llvmctx)
    (n : Nat) (offset : Nat) : M llvmctx (LLVM.Value llvmctx) := do
   -- TODO(bollu) : replace 8 with sizeof(void*)
   let out ← constIntUnsigned 8
   let out ← LLVM.buildMul builder out (← constIntUnsigned n) "" -- sizeof(void*)*n
   LLVM.buildAdd builder out (← constIntUnsigned offset) "" -- sizeof(void*)*n+offset

def emitSProj (builder : LLVM.Builder llvmctx)
    (z : VarId) (t : IRType) (n offset : Nat) (x : VarId) : M llvmctx Unit := do
  let (fnName, retty) ←
    match t with
    | IRType.float  => pure ("lean_ctor_get_float", ← LLVM.doubleTypeInContext llvmctx)
    | IRType.uint8  => pure ("lean_ctor_get_uint8", ← LLVM.i8Type llvmctx)
    | IRType.uint16 => pure ("lean_ctor_get_uint16", ←  LLVM.i16Type llvmctx)
    | IRType.uint32 => pure ("lean_ctor_get_uint32", ← LLVM.i32Type llvmctx)
    | IRType.uint64 => pure ("lean_ctor_get_uint64", ← LLVM.i64Type llvmctx)
    | _             => throw s!"Invalid type for lean_ctor_get: '{t}'"
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let xval ← emitLhsVal builder x
  let offset ← emitOffset builder n offset
  let fnty ← LLVM.functionType retty argtys
  let zval ← LLVM.buildCall2 builder fnty fn  #[xval, offset]
  emitLhsSlotStore builder z zval

def callLeanIsExclusive (builder : LLVM.Builder llvmctx)
    (closure : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_is_exclusive"
  let retty ← LLVM.i1Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let out ← LLVM.buildCall2 builder fnty fn  #[closure] retName
  LLVM.buildSextOrTrunc builder out (← LLVM.i8Type llvmctx)

def callLeanIsScalar (builder : LLVM.Builder llvmctx)
    (closure : LLVM.Value llvmctx) (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_is_scalar"
  let retty ← LLVM.i8Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn  #[closure] retName

def emitIsShared (builder : LLVM.Builder llvmctx) (z : VarId) (x : VarId) : M llvmctx Unit := do
    let xv ← emitLhsVal builder x
    let exclusive? ← callLeanIsExclusive builder xv
    let exclusive? ← LLVM.buildSextOrTrunc builder exclusive? (← LLVM.i1Type llvmctx)
    let shared? ← LLVM.buildNot builder exclusive?
    let shared? ← LLVM.buildSext builder shared? (← LLVM.i8Type llvmctx)
    emitLhsSlotStore builder z shared?

def emitBox (builder : LLVM.Builder llvmctx) (z : VarId) (x : VarId) (xType : IRType) : M llvmctx Unit := do
  let xv ← emitLhsVal builder x
  let (fnName, argTy, xv) ←
    match xType with
    | IRType.usize  => pure ("lean_box_usize", ← LLVM.size_tType llvmctx, xv)
    | IRType.uint32 => pure ("lean_box_uint32", ← LLVM.i32Type llvmctx, xv)
    | IRType.uint64 => pure ("lean_box_uint64", ← LLVM.size_tType llvmctx, xv)
    | IRType.float  => pure ("lean_box_float", ← LLVM.doubleTypeInContext llvmctx, xv)
    | _             => do
         -- sign extend smaller values into i64
         let xv ← LLVM.buildSext builder xv (← LLVM.size_tType llvmctx)
         pure ("lean_box", ← LLVM.size_tType llvmctx, xv)
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[argTy]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let zv ← LLVM.buildCall2 builder fnty fn  #[xv]
  emitLhsSlotStore builder z zv

def IRType.isIntegerType (t : IRType) : Bool :=
  match t with
  | .uint8 => true
  | .uint16 => true
  | .uint32 => true
  | .uint64 => true
  | .usize => true
  | _ => false

def callUnboxForType (builder : LLVM.Builder llvmctx)
    (t : IRType)
    (v : LLVM.Value llvmctx)
    (retName : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let (fnName, retty) ←
     match t with
     | IRType.usize  => pure ("lean_unbox_usize", ← toLLVMType t)
     | IRType.uint32 => pure ("lean_unbox_uint32", ← toLLVMType t)
     | IRType.uint64 => pure ("lean_unbox_uint64", ← toLLVMType t)
     | IRType.float  => pure ("lean_unbox_float", ← toLLVMType t)
     | _             => pure ("lean_unbox", ← LLVM.size_tType llvmctx)
  let argtys := #[← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[v] retName



def emitUnbox (builder : LLVM.Builder llvmctx)
    (z : VarId) (t : IRType) (x : VarId) (retName : String := "") : M llvmctx Unit := do
  let zval ← callUnboxForType builder t (← emitLhsVal builder x) retName
  -- NOTE(bollu) : note that lean_unbox only returns an i64, but we may need to truncate to
  -- smaller widths. see `phashmap` for an example of this occurring at calls to `lean_unbox`
  let zval ←
    if IRType.isIntegerType t
    then LLVM.buildSextOrTrunc builder zval (← toLLVMType t)
    else pure zval
  emitLhsSlotStore builder z zval

def emitReset (builder : LLVM.Builder llvmctx) (z : VarId) (n : Nat) (x : VarId) : M llvmctx Unit := do
  let xv ← emitLhsVal builder x
  let isExclusive ← callLeanIsExclusive builder xv
  let isExclusive ← buildLeanBoolTrue? builder isExclusive
  buildIfThenElse_ builder "isExclusive" isExclusive
   (fun builder => do
     let xv ← emitLhsVal builder x
     n.forM fun i => do
         callLeanCtorRelease builder xv (← constIntUnsigned i)
     emitLhsSlotStore builder z xv
     return ShouldForwardControlFlow.yes
   )
   (fun builder => do
      let xv ← emitLhsVal builder x
      callLeanDecRef builder xv
      let box0 ← callLeanBox builder (← constIntUnsigned 0) "box0"
      emitLhsSlotStore builder z box0
      return ShouldForwardControlFlow.yes
   )

def emitReuse (builder : LLVM.Builder llvmctx)
    (z : VarId) (x : VarId) (c : CtorInfo) (updtHeader : Bool) (ys : Array Arg) : M llvmctx Unit := do
  let xv ← emitLhsVal builder x
  let isScalar ← callLeanIsScalar builder xv
  let isScalar ← buildLeanBoolTrue? builder isScalar
  buildIfThenElse_ builder  "isScalar" isScalar
    (fun builder => do
      let cv ← emitAllocCtor builder c
      emitLhsSlotStore builder z cv
      return ShouldForwardControlFlow.yes
   )
   (fun builder => do
       let xv ← emitLhsVal builder x
       emitLhsSlotStore builder z xv
       if updtHeader then
          let zv ← emitLhsVal builder z
          callLeanCtorSetTag builder zv (← constIntUnsigned c.cidx)
       return ShouldForwardControlFlow.yes
   )
  emitCtorSetArgs builder z ys

def emitVDecl (builder : LLVM.Builder llvmctx) (z : VarId) (t : IRType) (v : Expr) : M llvmctx Unit := do
  match v with
  | Expr.ctor c ys      => emitCtor builder z c ys
  | Expr.reset n x      => emitReset builder z n x
  | Expr.reuse x c u ys => emitReuse builder z x c u ys
  | Expr.proj i x       => emitProj builder z i x
  | Expr.uproj i x      => emitUProj builder z i x
  | Expr.sproj n o x    => emitSProj builder z t n o x
  | Expr.fap c ys       => emitFullApp builder z c ys
  | Expr.pap c ys       => emitPartialApp builder z c ys
  | Expr.ap x ys        => emitApp builder z x ys
  | Expr.box t x        => emitBox builder z x t
  | Expr.unbox x        => emitUnbox builder z t x
  | Expr.isShared x     => emitIsShared builder z x
  | Expr.lit v          => let _ ← emitLit builder z t v

def declareVar (builder : LLVM.Builder llvmctx) (x : VarId) (t : IRType) : M llvmctx Unit := do
  let llvmty ← toLLVMType t
  let alloca ← LLVM.buildAlloca builder llvmty "varx"
  addVartoState x alloca llvmty

partial def declareVars (builder : LLVM.Builder llvmctx) (f : FnBody) : M llvmctx Unit := do
  match f with
  | FnBody.vdecl x t _ b => do
      declareVar builder x t
      declareVars builder b
  | FnBody.jdecl _ xs _ b => do
      for param in xs do declareVar builder param.x param.ty
      declareVars builder b
  | e => do
      if e.isTerminal then pure () else declareVars builder e.body

def emitTag (builder : LLVM.Builder llvmctx) (x : VarId) (xType : IRType) : M llvmctx (LLVM.Value llvmctx) := do
  if xType.isObj then do
    let xval ← emitLhsVal builder x
    callLeanObjTag builder xval
  else if xType.isScalar then do
    emitLhsVal builder x
  else
    throw "Do not know how to `emitTag` in general."

def emitSet (builder : LLVM.Builder llvmctx) (x : VarId) (i : Nat) (y : Arg) : M llvmctx Unit := do
  let fnName :=  "lean_ctor_set"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, ← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[← emitLhsVal builder x, ← constIntUnsigned i, (← emitArgVal builder y).2]

def emitUSet (builder : LLVM.Builder llvmctx) (x : VarId) (i : Nat) (y : VarId) : M llvmctx Unit := do
  let fnName :=  "lean_ctor_set_usize"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, ← LLVM.size_tType llvmctx]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[← emitLhsVal builder x, ← constIntUnsigned i, (← emitLhsVal builder y)]

def emitTailCall (builder : LLVM.Builder llvmctx) (f : FunId) (v : Expr) : M llvmctx Unit := do
   match v with
  | Expr.fap _ ys => do
    let llvmctx ← read
    let ps := llvmctx.mainParams
    unless ps.size == ys.size do throw s!"Invalid tail call. f:'{f}' v:'{v}'"
    let args ← ys.mapM (fun y => Prod.snd <$> emitArgVal builder y)
    let fn ← builderGetInsertionFn builder
    let call ← LLVM.buildCall2 builder (← getFunIdTy f) fn args
    -- TODO (bollu) : add 'musttail' attribute using the C API.
    LLVM.setTailCall call true -- mark as tail call
    let _ ← LLVM.buildRet builder call
  | _ => throw s!"EmitTailCall expects function application, found '{v}'"

def emitJmp (builder : LLVM.Builder llvmctx) (jp : JoinPointId) (xs : Array Arg) : M llvmctx Unit := do
 let llvmctx ← read
  let ps ← match llvmctx.jpMap.find? jp with
  | some ps => pure ps
  | none    => throw s!"Unknown join point {jp}"
  unless xs.size == ps.size do throw s!"Invalid goto, mismatched sizes between arguments, formal parameters."
  for (p, x)  in ps.zip xs do
    let (_xty, xv) ← emitArgVal builder x
    emitLhsSlotStore builder p.x xv
  let _ ← LLVM.buildBr builder (← emitJp jp)

def emitSSet (builder : LLVM.Builder llvmctx) (x : VarId) (n : Nat) (offset : Nat) (y : VarId) (t : IRType) : M llvmctx Unit := do
  let (fnName, setty) ←
  match t with
  | IRType.float  => pure ("lean_ctor_set_float", ← LLVM.doubleTypeInContext llvmctx)
  | IRType.uint8  => pure ("lean_ctor_set_uint8", ← LLVM.i8Type llvmctx)
  | IRType.uint16 => pure ("lean_ctor_set_uint16", ← LLVM.i16Type llvmctx)
  | IRType.uint32 => pure ("lean_ctor_set_uint32", ← LLVM.i32Type llvmctx)
  | IRType.uint64 => pure ("lean_ctor_set_uint64", ← LLVM.i64Type llvmctx)
  | _             => throw s!"invalid type for 'lean_ctor_set': '{t}'"
  let argtys := #[ ← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx, setty]
  let retty  ← LLVM.voidType llvmctx
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let xv ← emitLhsVal builder x
  let offset ← emitOffset builder n offset
  let yv ← emitLhsVal builder y
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[xv, offset, yv]

def emitDel (builder : LLVM.Builder llvmctx) (x : VarId) : M llvmctx Unit := do
  let argtys := #[ ← LLVM.voidPtrType llvmctx]
  let retty  ← LLVM.voidType llvmctx
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty "lean_free_object" argtys
  let xv ← emitLhsVal builder x
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[xv]

def emitSetTag (builder : LLVM.Builder llvmctx) (x : VarId) (i : Nat) : M llvmctx Unit := do
  let argtys := #[← LLVM.voidPtrType llvmctx, ← LLVM.size_tType llvmctx]
  let retty  ← LLVM.voidType llvmctx
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty "lean_ctor_set_tag" argtys
  let xv ← emitLhsVal builder x
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn  #[xv, ← constIntUnsigned i]

def ensureHasDefault' (alts : Array Alt) : Array Alt :=
  if alts.any Alt.isDefault then alts
  else
    let last := alts.back
    let alts := alts.pop
    alts.push (Alt.default last.body)

mutual
partial def emitCase (builder : LLVM.Builder llvmctx)
    (x : VarId) (xType : IRType) (alts : Array Alt) : M llvmctx Unit := do
  let oldBB ← LLVM.getInsertBlock builder
  -- NOTE: In this context, 'Zext' versus 'Sext' have a meaningful semantic difference.
  --       We perform a zero extend so that one-bit tags of `0/-1` actually extend to `0/1`
  --       in 64-bit space.
  let tag ← emitTag builder x xType
  let tag ← LLVM.buildZext builder tag (← LLVM.i64Type llvmctx)
  let alts := ensureHasDefault' alts
  let defaultBB ← builderAppendBasicBlock builder s!"case_{xType}_default"
  let numCasesHint := alts.size
  let switch ← LLVM.buildSwitch builder tag defaultBB (UInt64.ofNat numCasesHint)
  alts.forM fun alt => do
    match alt with
    | Alt.ctor c b  =>
       let destbb ← builderAppendBasicBlock builder s!"case_{xType}_{c.name}_{c.cidx}"
       LLVM.addCase switch (← constIntUnsigned c.cidx) destbb
       LLVM.positionBuilderAtEnd builder destbb
       emitFnBody builder b
    | Alt.default b =>
       LLVM.positionBuilderAtEnd builder defaultBB
       emitFnBody builder b
  LLVM.clearInsertionPosition builder
  LLVM.positionBuilderAtEnd builder oldBB -- reset state to previous insertion point.

-- NOTE:  emitJP promises to keep the builder context untouched.
partial def emitJDecl (builder : LLVM.Builder llvmctx)
    (jp : JoinPointId) (_ps : Array Param) (b : FnBody) : M llvmctx Unit := do
  let oldBB ← LLVM.getInsertBlock builder
  let jpbb ← builderAppendBasicBlock builder s!"jp_{jp.idx}"
  addJpTostate jp jpbb
  LLVM.positionBuilderAtEnd builder jpbb
  -- NOTE(bollu) : Note that we declare the slots for the variables that are inside
  --              the join point body before emitting the join point body.
  --              This ensures reachability via dominance.
  -- TODO(bollu) : Eliminate the need entirely for 'alloca'/slots by generating SSA phi nodes
  --              directly as discussed with digamma(Mario Carneiro <di.gama@gmail.com>)
  declareVars builder b
  emitBlock builder b
  LLVM.positionBuilderAtEnd builder oldBB -- reset state

partial def emitUnreachable (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype  (← getLLVMModule) retty "lean_internal_panic_unreachable" argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn #[]
  let _ ← LLVM.buildUnreachable builder

partial def emitBlock (builder : LLVM.Builder llvmctx) (b : FnBody) : M llvmctx Unit := do
  match b with
  | FnBody.jdecl j xs  v b      =>
       emitJDecl builder j xs v
       emitBlock builder b
  | d@(FnBody.vdecl x t v b)   => do
    let llvmctx ← read
    if isTailCallTo llvmctx.mainFn d then
      emitTailCall builder llvmctx.mainFn v
    else
      emitVDecl builder x t v
      emitBlock builder b
  | FnBody.inc x n c p b       =>
    unless p do emitInc builder x n c
    emitBlock builder b
  | FnBody.dec x n c p b       =>
    unless p do emitDec builder x n c
    emitBlock builder b
  | FnBody.del x b             =>  emitDel builder x; emitBlock builder b
  | FnBody.setTag x i b        =>  emitSetTag builder x i; emitBlock builder b
  | FnBody.set x i y b         => emitSet builder x i y; emitBlock builder b
  | FnBody.uset x i y b        => emitUSet builder x i y; emitBlock builder b
  | FnBody.sset x i o y t b    => emitSSet builder x i o y t; emitBlock builder b
  | FnBody.mdata _ b           => emitBlock builder b
  | FnBody.ret x               => do
      let (_xty, xv) ← emitArgVal builder x "ret_val"
      let _ ← LLVM.buildRet builder xv
  | FnBody.case _ x xType alts =>
     emitCase builder x xType alts
  | FnBody.jmp j xs            =>
     emitJmp builder j xs
  | FnBody.unreachable         => emitUnreachable builder

partial def emitFnBody  (builder : LLVM.Builder llvmctx)  (b : FnBody) : M llvmctx Unit := do
  declareVars builder b
  emitBlock builder b

end

def emitFnArgs (builder : LLVM.Builder llvmctx)
    (needsPackedArgs? : Bool)  (llvmfn : LLVM.Value llvmctx) (params : Array Param) : M llvmctx Unit := do
  if needsPackedArgs? then do
      let argsp ← LLVM.getParam llvmfn 0 -- lean_object **args
      for i in List.range params.size do
          let param := params[i]!
          -- argsi := (args + i)
          let argsi ← LLVM.buildGEP2 builder (← LLVM.voidPtrType llvmctx) argsp #[← constIntUnsigned i] s!"packed_arg_{i}_slot"
          let llvmty ← toLLVMType param.ty
          -- pv := *(argsi) = *(args + i)
          let pv ← LLVM.buildLoad2 builder llvmty argsi
          -- slot for arg[i] which is always void* ?
          let alloca ← LLVM.buildAlloca builder llvmty s!"arg_{i}"
          LLVM.buildStore builder pv alloca
          addVartoState params[i]!.x alloca llvmty
  else
      let n ← LLVM.countParams llvmfn
      for i in (List.range n.toNat) do
        let llvmty ← toLLVMType params[i]!.ty
        let alloca ← LLVM.buildAlloca builder  llvmty s!"arg_{i}"
        let arg ← LLVM.getParam llvmfn (UInt64.ofNat i)
        let _ ← LLVM.buildStore builder arg alloca
        addVartoState params[i]!.x alloca llvmty

def emitDeclAux (mod : LLVM.Module llvmctx) (builder : LLVM.Builder llvmctx) (d : Decl) : M llvmctx Unit := do
  let env ← getEnv
  let (_, jpMap) := mkVarJPMaps d
  withReader (fun llvmctx => { llvmctx with jpMap := jpMap }) do
  unless hasInitAttr env d.name do
    match d with
    | .fdecl (f := f) (xs := xs) (type := t) (body := b) .. =>
      let baseName ← toCName f
      let name := if xs.size > 0 then baseName else "_init_" ++ baseName
      let retty ← toLLVMType t
      let mut argtys := #[]
      let needsPackedArgs? := xs.size > closureMaxArgs && isBoxedName d.name
      if needsPackedArgs? then
          argtys := #[← LLVM.pointerType (← LLVM.voidPtrType llvmctx)]
      else
        for x in xs do
          argtys := argtys.push (← toLLVMType x.ty)
      let fnty ← LLVM.functionType retty argtys (isVarArg := false)
      let llvmfn ← LLVM.getOrAddFunction mod name fnty
      -- set linkage and visibility
      -- TODO: consider refactoring these into a separate concept (e.g. 'setLinkageAndVisibility')
      --       Find the spots where this refactor needs to happen by grepping for 'LEAN_EXPORT'
      --       in the C backend
      if xs.size == 0 then
        LLVM.setVisibility llvmfn LLVM.Visibility.hidden -- "static "
      else
        LLVM.setDLLStorageClass llvmfn LLVM.DLLStorageClass.export  -- LEAN_EXPORT: make symbol visible to the interpreter
      withReader (fun llvmctx => { llvmctx with mainFn := f, mainParams := xs }) do
        set { var2val := default, jp2bb := default : EmitLLVM.State llvmctx } -- flush variable map
        let bb ← LLVM.appendBasicBlockInContext llvmctx llvmfn "entry"
        LLVM.positionBuilderAtEnd builder bb
        emitFnArgs builder needsPackedArgs? llvmfn xs
        emitFnBody builder b
      pure ()
    | _ => pure ()

def emitDecl (mod : LLVM.Module llvmctx) (builder : LLVM.Builder llvmctx) (d : Decl) : M llvmctx Unit := do
  let d := d.normalizeIds -- ensure we don't have gaps in the variable indices
  try
    emitDeclAux mod builder d
    return ()
  catch err =>
    throw (s!"emitDecl:\ncompiling:\n{d}\nerr:\n{err}\n")

def emitFns (mod : LLVM.Module llvmctx) (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let env ← getEnv
  let decls := getDecls env
  decls.reverse.forM (emitDecl mod builder)

def callIODeclInitFn (builder : LLVM.Builder llvmctx)
    (initFnName : String)
    (world : LLVM.Value llvmctx): M llvmctx (LLVM.Value llvmctx) := do
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[← LLVM.voidPtrType llvmctx]
  let fn ← getOrCreateFunctionPrototype  (← getLLVMModule) retty initFnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[world]

def callPureDeclInitFn (builder : LLVM.Builder llvmctx)
    (initFnName : String)
    (retty : LLVM.LLVMType llvmctx): M llvmctx (LLVM.Value llvmctx) := do
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype  (← getLLVMModule) retty initFnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[]

def emitDeclInit (builder : LLVM.Builder llvmctx)
    (parentFn : LLVM.Value llvmctx) (d : Decl) : M llvmctx Unit := do
  let env ← getEnv
  if isIOUnitInitFn env d.name then do
    let world ← callLeanIOMkWorld builder
    let resv ← callIODeclInitFn builder (← toCName d.name) world
    let err? ← callLeanIOResultIsError builder resv "is_error"
    buildIfThen_ builder s!"init_{d.name}_isError" err?
      (fun builder => do
        let _ ← LLVM.buildRet builder resv
        pure ShouldForwardControlFlow.no)
    -- TODO (bollu) : emit lean_dec_ref. For now, it does not matter.
  else if d.params.size == 0 then
    match getInitFnNameFor? env d.name with
    | some initFn =>
      let llvmty ← toLLVMType d.resultType
      let dslot ←  LLVM.getOrAddGlobal (← getLLVMModule) (← toCName d.name) llvmty
      LLVM.setInitializer dslot (← LLVM.getUndef llvmty)
      let initBB ← builderAppendBasicBlock builder s!"do_{d.name}_init"
      let restBB ← builderAppendBasicBlock builder s!"post_{d.name}_init"
      let checkBuiltin? := getBuiltinInitFnNameFor? env d.name |>.isSome
      if checkBuiltin? then
        -- `builtin` is set to true if the initializer is part of the executable,
        -- and not loaded dynamically.
        let builtinParam ← LLVM.getParam parentFn 0
        let cond ← buildLeanBoolTrue? builder builtinParam "is_builtin_true"
        let _ ← LLVM.buildCondBr builder cond initBB restBB
       else
        let _ ← LLVM.buildBr builder initBB
      LLVM.positionBuilderAtEnd builder initBB
      let world ← callLeanIOMkWorld builder
      let resv ← callIODeclInitFn builder (← toCName initFn) world
      let err? ← callLeanIOResultIsError builder resv s!"{d.name}_is_error"
      buildIfThen_ builder s!"init_{d.name}_isError" err?
        (fun builder => do
          let _ ← LLVM.buildRet builder resv
          pure ShouldForwardControlFlow.no)
      if d.resultType.isScalar then
        let dval ← callLeanIOResultGetValue builder resv s!"{d.name}_res"
        let dval ← callUnboxForType builder d.resultType dval
        LLVM.buildStore builder dval dslot
      else
         let dval ← callLeanIOResultGetValue builder resv s!"{d.name}_res"
         LLVM.buildStore builder dval dslot
         callLeanMarkPersistentFn builder dval
      let _ ← LLVM.buildBr builder restBB
      LLVM.positionBuilderAtEnd builder restBB
    | none => do
      let llvmty ← toLLVMType d.resultType
      let dslot ←  LLVM.getOrAddGlobal (← getLLVMModule) (← toCName d.name) llvmty
      LLVM.setInitializer dslot (← LLVM.getUndef llvmty)
      let dval ← callPureDeclInitFn builder (← toCInitName d.name) (← toLLVMType d.resultType)
      LLVM.buildStore builder dval dslot
      if d.resultType.isObj then
         callLeanMarkPersistentFn builder dval

def callModInitFn (builder : LLVM.Builder llvmctx)
    (modName : Name) (input world : LLVM.Value llvmctx) (retName : String): M llvmctx (LLVM.Value llvmctx) := do
  let fnName := mkModuleInitializationFunctionName modName
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[ (← LLVM.i8Type llvmctx), (← LLVM.voidPtrType llvmctx)]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[input, world] retName

def emitInitFn (mod : LLVM.Module llvmctx) (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let env ← getEnv
  let modName ← getModName

  let initFnTy ← LLVM.functionType (← LLVM.voidPtrType llvmctx) #[ (← LLVM.i8Type llvmctx), (← LLVM.voidPtrType llvmctx)] (isVarArg := false)
  let initFn ← LLVM.getOrAddFunction mod (mkModuleInitializationFunctionName modName) initFnTy
  LLVM.setDLLStorageClass initFn LLVM.DLLStorageClass.export  -- LEAN_EXPORT
  let entryBB ← LLVM.appendBasicBlockInContext llvmctx initFn "entry"
  LLVM.positionBuilderAtEnd builder entryBB
  let ginit?ty := ← LLVM.i1Type llvmctx
  let ginit?slot ← LLVM.getOrAddGlobal mod (modName.mangle ++ "_G_initialized") ginit?ty
  LLVM.setVisibility ginit?slot LLVM.Visibility.hidden -- static
  LLVM.setInitializer ginit?slot (← LLVM.constFalse llvmctx)
  let ginit?v ← LLVM.buildLoad2 builder ginit?ty ginit?slot "init_v"
  buildIfThen_ builder "isGInitialized" ginit?v
    (fun builder => do
      let box0 ← callLeanBox builder (← LLVM.constIntUnsigned llvmctx 0) "box0"
      let out ← callLeanIOResultMKOk builder box0 "retval"
      let _ ← LLVM.buildRet builder out
      pure ShouldForwardControlFlow.no)
  LLVM.buildStore builder (← LLVM.constTrue llvmctx) ginit?slot

  env.imports.forM fun import_ => do
    let builtin ← LLVM.getParam initFn 0
    let world ← callLeanIOMkWorld builder
    let res ← callModInitFn builder import_.module builtin world ("res_" ++ import_.module.mangle)
    let err? ← callLeanIOResultIsError builder res ("res_is_error_"  ++ import_.module.mangle)
    buildIfThen_ builder ("IsError" ++ import_.module.mangle) err?
      (fun builder => do
        let _ ← LLVM.buildRet builder res
        pure ShouldForwardControlFlow.no)
    callLeanDecRef builder res
  let decls := getDecls env
  decls.reverse.forM (emitDeclInit builder initFn)
  let box0 ← callLeanBox builder (← LLVM.constIntUnsigned llvmctx 0) "box0"
  let out ← callLeanIOResultMKOk builder box0 "retval"
  let _ ← LLVM.buildRet builder out

def callLeanInitialize (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_initialize"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fnty ← LLVM.functionType retty argtys
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let _ ← LLVM.buildCall2 builder fnty fn #[]

def callLeanInitializeRuntimeModule (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_initialize_runtime_module"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fnty ← LLVM.functionType retty argtys
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let _ ← LLVM.buildCall2 builder fnty fn #[]

def callLeanSetPanicMessages (builder : LLVM.Builder llvmctx)
    (enable? : LLVM.Value llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_set_panic_messages"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.i1Type llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn #[enable?]

def callLeanIOMarkEndInitialization (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_io_mark_end_initialization"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn #[]

def callLeanIOResultIsOk (builder : LLVM.Builder llvmctx)
    (arg : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_io_result_is_ok"
  let retty ← LLVM.i1Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn #[arg] name

def callLeanInitTaskManager (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_init_task_manager"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
   let _ ← LLVM.buildCall2 builder fnty fn #[]

def callLeanFinalizeTaskManager (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let fnName :=  "lean_finalize_task_manager"
  let retty ← LLVM.voidPtrType llvmctx
  let argtys := #[]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
   let _ ← LLVM.buildCall2 builder fnty fn #[]

def callLeanUnboxUint32 (builder : LLVM.Builder llvmctx)
    (v : LLVM.Value llvmctx) (name : String := "") : M llvmctx (LLVM.Value llvmctx) := do
  let fnName :=  "lean_unbox_uint32"
  let retty ← LLVM.i32Type llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  LLVM.buildCall2 builder fnty fn  #[v] name

def callLeanIOResultShowError (builder : LLVM.Builder llvmctx)
    (v : LLVM.Value llvmctx) (name : String := "") : M llvmctx Unit := do
  let fnName :=  "lean_io_result_show_error"
  let retty ← LLVM.voidType llvmctx
  let argtys := #[ ← LLVM.voidPtrType llvmctx ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty fnName argtys
  let fnty ← LLVM.functionType retty argtys
  let _ ← LLVM.buildCall2 builder fnty fn #[v] name

def callLeanMainFn (builder : LLVM.Builder llvmctx)
    (argv? : Option (LLVM.Value llvmctx))
    (world : LLVM.Value llvmctx)
    (name : String) : M llvmctx (LLVM.Value llvmctx) := do
  let retty ← LLVM.voidPtrType llvmctx
  let voidptr ← LLVM.voidPtrType llvmctx
  let argtys := if argv?.isSome then #[ voidptr, voidptr ] else #[ voidptr ]
  let fn ← getOrCreateFunctionPrototype (← getLLVMModule) retty leanMainFn argtys
  let fnty ← LLVM.functionType retty argtys
  let args := match argv? with
              | .some argv => #[argv, world]
              | .none => #[world]
  LLVM.buildCall2 builder fnty fn args name

def emitMainFn (mod : LLVM.Module llvmctx) (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  let d ← getDecl `main
  let xs ← match d with
   | .fdecl (xs := xs) .. => pure xs
   | _ =>  throw "Function declaration expected for 'main'"

  unless xs.size == 2 || xs.size == 1 do throw s!"Invalid main function, main expected to have '2' or '1' arguments, found '{xs.size}' arguments"
  let env ← getEnv
  let usesLeanAPI := usesModuleFrom env `Lean
  let mainTy ← LLVM.functionType (← LLVM.i64Type llvmctx)
      #[(← LLVM.i64Type llvmctx), (← LLVM.pointerType (← LLVM.voidPtrType llvmctx))]
  let main ← LLVM.getOrAddFunction mod "main" mainTy
  let entry ← LLVM.appendBasicBlockInContext llvmctx main "entry"
  LLVM.positionBuilderAtEnd builder entry
  /-
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  #endif
  -/
  let inty ← LLVM.voidPtrType llvmctx
  let inslot ← LLVM.buildAlloca builder (← LLVM.pointerType inty) "in"
  let resty ← LLVM.voidPtrType llvmctx
  let res ← LLVM.buildAlloca builder (← LLVM.pointerType resty) "res"
  if usesLeanAPI then callLeanInitialize builder else callLeanInitializeRuntimeModule builder
    /- We disable panic messages because they do not mesh well with extracted closed terms.
        See issue #534. We can remove this workaround after we implement issue #467. -/
  callLeanSetPanicMessages builder (← LLVM.constFalse llvmctx)
  let world ← callLeanIOMkWorld builder
  let resv ← callModInitFn builder (← getModName) (← LLVM.constInt8 llvmctx 1) world ((← getModName).toString ++ "_init_out")
  let _ ← LLVM.buildStore builder resv res

  callLeanSetPanicMessages builder (← LLVM.constTrue llvmctx)
  callLeanIOMarkEndInitialization builder

  let resv ← LLVM.buildLoad2 builder resty res "resv"
  let res_is_ok ← callLeanIOResultIsOk builder resv "res_is_ok"
  buildIfThen_ builder "resIsOkBranches"  res_is_ok
    (fun builder => do -- then clause of the builder)
      callLeanDecRef builder resv
      callLeanInitTaskManager builder
      if xs.size == 2 then
        let inv ← callLeanBox builder (← LLVM.constInt (← LLVM.size_tType llvmctx) 0) "inv"
        let _ ← LLVM.buildStore builder inv inslot
        let ity ← LLVM.size_tType llvmctx
        let islot ← LLVM.buildAlloca builder ity "islot"
        let argcval ← LLVM.getParam main 0
        let argvval ← LLVM.getParam main 1
        LLVM.buildStore builder argcval islot
        buildWhile_ builder "argv"
          (condcodegen := fun builder => do
            let iv ← LLVM.buildLoad2 builder ity islot "iv"
            let i_gt_1 ← LLVM.buildICmp builder LLVM.IntPredicate.UGT iv (← constIntUnsigned 1) "i_gt_1"
            return i_gt_1)
          (bodycodegen := fun builder => do
            let iv ← LLVM.buildLoad2 builder ity islot "iv"
            let iv_next ← LLVM.buildSub builder iv (← constIntUnsigned 1) "iv.next"
            LLVM.buildStore builder iv_next islot
            let nv ← callLeanAllocCtor builder 1 2 0 "nv"
            let argv_i_next_slot ← LLVM.buildGEP2 builder (← LLVM.voidPtrType llvmctx) argvval #[iv_next] "argv.i.next.slot"
            let argv_i_next_val ← LLVM.buildLoad2 builder (← LLVM.voidPtrType llvmctx) argv_i_next_slot "argv.i.next.val"
            let argv_i_next_val_str ← callLeanMkString builder argv_i_next_val "arg.i.next.val.str"
            callLeanCtorSet builder nv (← constIntUnsigned 0) argv_i_next_val_str
            let inv ← LLVM.buildLoad2 builder inty inslot "inv"
            callLeanCtorSet builder nv (← constIntUnsigned 1) inv
            LLVM.buildStore builder nv inslot)
        let world ← callLeanIOMkWorld builder
        let inv ← LLVM.buildLoad2 builder inty inslot "inv"
        let resv ← callLeanMainFn builder (argv? := .some inv) (world := world) "resv"
        let _ ← LLVM.buildStore builder resv res
        pure ShouldForwardControlFlow.yes
      else
          let world ← callLeanIOMkWorld builder
          let resv ← callLeanMainFn builder (argv? := .none) (world := world) "resv"
          let _ ← LLVM.buildStore builder resv res
          pure ShouldForwardControlFlow.yes
  )

  -- `IO _`
  let retTy := env.find? `main |>.get! |>.type |>.getForallBody
  -- either `UInt32` or `(P)Unit`
  let retTy := retTy.appArg!
  -- finalize at least the task manager to avoid leak sanitizer false positives
  -- from tasks outliving the main thread
  callLeanFinalizeTaskManager builder
  let resv ← LLVM.buildLoad2 builder resty res "resv"
  let res_is_ok ← callLeanIOResultIsOk builder resv "res_is_ok"
  buildIfThenElse_ builder "res.is.ok" res_is_ok
    (fun builder => -- then builder
      if retTy.constName? == some ``UInt32 then do
        let resv ← LLVM.buildLoad2 builder resty res "resv"
        let retv ← callLeanUnboxUint32 builder (← callLeanIOResultGetValue builder resv "io_val") "retv"
        let retv ← LLVM.buildSext builder retv (← LLVM.i64Type llvmctx) "retv_sext"
        callLeanDecRef builder resv
        let _ ← LLVM.buildRet builder retv
        pure ShouldForwardControlFlow.no
      else do
        callLeanDecRef builder resv
        let _ ← LLVM.buildRet builder (← LLVM.constInt64 llvmctx 0)
        pure ShouldForwardControlFlow.no

    )
    (fun builder => do -- else builder
        let resv ← LLVM.buildLoad2 builder resty res "resv"
        callLeanIOResultShowError builder resv
        callLeanDecRef builder resv
        let _ ← LLVM.buildRet builder (← LLVM.constInt64 llvmctx 1)
        pure ShouldForwardControlFlow.no)
  -- at the merge
  let _ ← LLVM.buildUnreachable builder

def hasMainFn : M llvmctx Bool := do
  let env ← getEnv
  let decls := getDecls env
  return decls.any (fun d => d.name == `main)

def emitMainFnIfNeeded (mod : LLVM.Module llvmctx) (builder : LLVM.Builder llvmctx) : M llvmctx Unit := do
  if (← hasMainFn) then emitMainFn mod builder

def main : M llvmctx Unit := do
  emitFnDecls
  let builder ← LLVM.createBuilderInContext llvmctx
  emitFns (← getLLVMModule) builder
  emitInitFn (← getLLVMModule) builder
  emitMainFnIfNeeded (← getLLVMModule) builder
end EmitLLVM

def getLeanHBcPath : IO System.FilePath := do
  return (← getLibDir (← getBuildDir)) / "lean.h.bc"

/-- Get the names of all global symbols in the module -/
partial def getModuleGlobals (mod : LLVM.Module llvmctx) : IO (Array (LLVM.Value llvmctx)) := do
  let rec go (v : LLVM.Value llvmctx) (acc : Array (LLVM.Value llvmctx)) : IO (Array (LLVM.Value llvmctx)) := do
    if v.isNull then return acc
    else go (← LLVM.getNextGlobal v) (acc.push v)
  go (← LLVM.getFirstGlobal mod) #[]

/-- Get the names of all global functions in the module -/
partial def getModuleFunctions (mod : LLVM.Module llvmctx) : IO (Array (LLVM.Value llvmctx)) := do
  let rec go (v : LLVM.Value llvmctx) (acc : Array (LLVM.Value llvmctx)) : IO (Array (LLVM.Value llvmctx)) := do
    if v.isNull then return acc
    else go (← LLVM.getNextFunction v) (acc.push v)
  go (← LLVM.getFirstFunction mod) #[]

/--
`emitLLVM` is the entrypoint for the lean shell to code generate LLVM.
-/
@[export lean_ir_emit_llvm]
def emitLLVM (env : Environment) (modName : Name) (filepath : String) : IO Unit := do
  LLVM.llvmInitializeTargetInfo
  let llvmctx ← LLVM.createContext
  let module ← LLVM.createModule llvmctx modName.toString
  let emitLLVMCtx : EmitLLVM.Context llvmctx := {env := env, modName := modName, llvmmodule := module}
  let initState := { var2val := default, jp2bb := default : EmitLLVM.State llvmctx}
  let out? ← ((EmitLLVM.main (llvmctx := llvmctx)).run initState).run emitLLVMCtx
  match out? with
  | .ok _ => do
         let membuf ← LLVM.createMemoryBufferWithContentsOfFile (← getLeanHBcPath).toString
         let modruntime ← LLVM.parseBitcode llvmctx membuf
         /- It is important that we extract the names here because
            pointers into modruntime get invalidated by linkModules -/
         let runtimeGlobals ← (← getModuleGlobals modruntime).mapM (·.getName)
         let filter func := do
           -- | Do not insert internal linkage for
           -- intrinsics such as `@llvm.umul.with.overflow.i64` which clang generates, and also
           -- for declarations such as `lean_inc_ref_cold` which are externally defined.
           if (← LLVM.isDeclaration func) then
             return none
           else
             return some (← func.getName)
         let runtimeFunctions ← (← getModuleFunctions modruntime).filterMapM filter
         LLVM.linkModules (dest := emitLLVMCtx.llvmmodule) (src := modruntime)
         -- Mark every global and function as having internal linkage.
         for name in runtimeGlobals do
           let some global ← LLVM.getNamedGlobal emitLLVMCtx.llvmmodule name
              | throw <| IO.Error.userError s!"ERROR: linked module must have global from runtime module: '{name}'"
           LLVM.setLinkage global LLVM.Linkage.internal
         for name in runtimeFunctions do
           let some fn ← LLVM.getNamedFunction emitLLVMCtx.llvmmodule name
              | throw <| IO.Error.userError s!"ERROR: linked module must have function from runtime module: '{name}'"
           LLVM.setLinkage fn LLVM.Linkage.internal
         LLVM.writeBitcodeToFile emitLLVMCtx.llvmmodule filepath
         LLVM.disposeModule emitLLVMCtx.llvmmodule
  | .error err => throw (IO.Error.userError err)
end Lean.IR
