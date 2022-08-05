/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Runtime
import Lean.Compiler.NameMangling
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.Boxing

open Lean.IR.ExplicitBoxing (isBoxedName)


namespace Lean.IR

def leanMainFn := "_lean_main"


namespace LLVM

inductive Ty where
| int: Nat → Ty
| float: Nat → Ty
| ptr: Ty → Ty

def Ty.i32: Ty := Ty.int 32
def Ty.i1: Ty := Ty.int 1
def Ty.i8: Ty := Ty.int 8
def Ty.i8ptr: Ty := .ptr <| Ty.i8

structure BasicBlock where
-- structure Function where
-- structure GlobalValue where
structure Context where
structure Module where
structure Builder where
structure LLVMType where
structure Value where

-- A raw pointer to a C object, whose Lean representation
-- is given by α
opaque Ptr (α: Type): Type := Unit

@[extern "lean_llvm_create_context"]
opaque createContext: IO (Ptr Context)

@[extern "lean_llvm_create_module"]
opaque createModule (ctx: @&Ptr Context) (name: @&String): IO (Ptr Module)


@[extern "lean_llvm_module_to_string"]
opaque moduletoString (m: @&Ptr Module): IO String

@[extern "lean_llvm_write_bitcode_to_file"]
opaque writeBitcodeToFile(m: @&Ptr Module) (path: @&String): IO Unit

@[extern "lean_llvm_add_function"]
opaque addFunction(m: @&Ptr Module) (name: @&String) (type: @&Ptr LLVMType): IO (Ptr Value)

@[extern "lean_llvm_get_named_function"]
opaque getNamedFunction(m: @&Ptr Module) (name: @&String): IO (Option (Ptr Value))

@[extern "lean_llvm_add_global"]
opaque addGlobal(m: @&Ptr Module) (name: @&String) (type: @&Ptr LLVMType): IO (Ptr Value)

@[extern "lean_llvm_get_named_global"]
opaque getNamedGlobal(m: @&Ptr Module) (name: @&String): IO (Option (Ptr Value))

@[extern "lean_llvm_set_initializer"]
opaque setInitializer (glbl: @&Ptr Value) (val: @&Ptr Value): IO Unit

@[extern "lean_llvm_function_type"]
opaque functionType(retty: @&Ptr LLVMType) (args: @&Array (Ptr LLVMType)) (isVarArg: Bool := false): IO (Ptr LLVMType)

@[extern "lean_llvm_void_type_in_context"]
opaque voidTypeInContext (ctx: @&Ptr Context): IO (Ptr LLVMType)

@[extern "lean_llvm_int_type_in_context"]
opaque intTypeInContext (ctx: @&Ptr Context) (width: UInt64): IO (Ptr LLVMType)

@[extern "lean_llvm_float_type_in_context"]
opaque floatTypeInContext (ctx: @&Ptr Context): IO (Ptr LLVMType)

@[extern "lean_llvm_double_type_in_context"]
opaque doubleTypeInContext (ctx: @&Ptr Context): IO (Ptr LLVMType)

@[extern "lean_llvm_pointer_type"]
opaque pointerType (ty: @&Ptr LLVMType): IO (Ptr LLVMType)

@[extern "lean_llvm_create_builder_in_context"]
opaque createBuilderInContext (ctx: @&Ptr Context): IO (Ptr Builder)

@[extern "lean_llvm_append_basic_block_in_context"]
opaque appendBasicBlockInContext (ctx: @&Ptr Context) (fn: @& Ptr Value) (name: @&String): IO (Ptr BasicBlock)

@[extern "lean_llvm_position_builder_at_end"]
opaque positionBuilderAtEnd (builder: @&Ptr Builder) (bb: @& Ptr BasicBlock): IO Unit

-- @[extern "lean_llvm_build_call2"]
-- opaque buildCall2 (builder: @&Ptr Builder) (fnty: @&Ptr LLVMType) (fn: @&Ptr Value) (args: @&Array (Ptr Value)) (name: @&String): IO (Ptr Value)

@[extern "lean_llvm_build_call"]
opaque buildCall (builder: @&Ptr Builder) (fn: @&Ptr Value) (args: @&Array (Ptr Value)) (name: @&String): IO (Ptr Value)

@[extern "lean_llvm_build_cond_br"]
opaque buildCondBr (builder: @&Ptr Builder) (if_: @&Ptr Value) (thenbb: @&Ptr BasicBlock) (elsebb: @&Ptr BasicBlock): IO (Ptr Value)

@[extern "lean_llvm_build_br"]
opaque buildBr (builder: @&Ptr Builder) (bb: @&Ptr BasicBlock): IO (Ptr Value)

@[extern "lean_llvm_build_alloca"]
opaque buildAlloca (builder: @&Ptr Builder) (ty: @&Ptr LLVMType) (name: @&String): IO (Ptr Value)

@[extern "lean_llvm_build_load"]
opaque buildLoad (builder: @&Ptr Builder) (val: @&Ptr Value) (name: @&String): IO (Ptr Value)

@[extern "lean_llvm_build_store"]
opaque buildStore (builder: @&Ptr Builder) (val: @&Ptr Value) (store_loc_ptr: @&Ptr Value): IO Unit

@[extern "lean_llvm_build_ret"]
opaque buildRet (builder: @&Ptr Builder) (val: @&Ptr Value): IO (Ptr Value)

@[extern "lean_llvm_build_unreachable"]
opaque buildUnreachable (builder: @&Ptr Builder): IO (Ptr Value)

@[extern "lean_llvm_get_insert_block"]
opaque getInsertBlock (builder: @&Ptr Builder): IO (Ptr BasicBlock)

@[extern "lean_llvm_get_basic_block_parent"]
opaque getBasicBlockParent (bb: @&Ptr BasicBlock): IO (Ptr Value)


@[extern "lean_llvm_type_of"]
opaque typeOf (val: @&Ptr Value): IO (Ptr LLVMType)

@[extern "lean_llvm_const_int"]
opaque constInt (intty: @&Ptr LLVMType) (value: @&UInt64) (signExtend: @Bool := false): IO (Ptr Value)


@[extern "lean_llvm_print_module_to_string"]
opaque printModuletoString (mod: @&Ptr Module): IO (String)

@[extern "lean_llvm_print_module_to_file"]
opaque printModuletoFile (mod: @&Ptr Module) (file: @&String): IO Unit

@[extern "llvm_count_params"]
opaque countParams (fn: @&Ptr Function): UInt64 -- will this cause problems..?

@[extern "llvm_get_param"]
opaque getParam (fn: @&Ptr Function) (ix: UInt64): IO (Ptr Value)

-- Helper to add a function if it does not exist, and to return the function handle if it does.
def getOrAddFunction(m: Ptr Module) (name: String) (type: Ptr LLVMType): IO (Ptr Value) :=  do
  match (← getNamedFunction m name) with
  | .some fn => return fn
  | .none => addFunction m name type

def getOrAddGlobal(m: Ptr Module) (name: String) (type: Ptr LLVMType): IO (Ptr Value) :=  do
  match (← getNamedGlobal m name) with
  | .some fn => return fn
  | .none => addGlobal m name type


def i1Type (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  LLVM.intTypeInContext ctx 1

def i8Type (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  LLVM.intTypeInContext ctx 8

def i32Type (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  LLVM.intTypeInContext ctx 32


def i64Type (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  LLVM.intTypeInContext ctx 64

def voidPtrType (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  do LLVM.pointerType (← LLVM.intTypeInContext ctx 8)

def i8PtrType (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) := voidPtrType ctx

-- TODO: instantiate target triple and find out what size_t is.
def size_tTypeInContext (ctx: @&Ptr Context): IO (Ptr LLVMType) := i64Type ctx

def True (ctx: Ptr Context): IO (Ptr Value) :=
  do constInt (← i1Type ctx) 1 (signExtend := false)

def False (ctx: Ptr Context): IO (Ptr Value) :=
  do constInt (← i1Type ctx) 0 (signExtend := false)

def constInt' (ctx: Ptr Context) (width: UInt64) (value: UInt64) (signExtend: Bool := false): IO (Ptr Value) :=
 do constInt (← LLVM.intTypeInContext ctx width) value signExtend

def constInt1 (ctx: Ptr Context) (value: UInt64) (signExtend: Bool := false): IO (Ptr Value) :=
  constInt' ctx 1 value signExtend

def constInt8 (ctx: Ptr Context) (value: UInt64) (signExtend: Bool := false): IO (Ptr Value) :=
  constInt' ctx 8 value signExtend

def constInt64 (ctx: Ptr Context) (value: UInt64) (signExtend: Bool := false): IO (Ptr Value) :=
  constInt' ctx 64 value signExtend

def constIntUnsigned (ctx: Ptr Context) (value: UInt64) (signExtend: Bool := false): IO (Ptr Value) :=
  constInt' ctx 64 value signExtend

-- infer the type of the called function and then build the call
-- def buildCallWithInferredType ()

end LLVM

namespace EmitLLVM

structure Context where
  env        : Environment
  modName    : Name
  jpMap      : JPParamsMap := {}
  mainFn     : FunId := default
  mainParams : Array Param := #[]
  llvmctx : LLVM.Ptr LLVM.Context
  llvmmodule : LLVM.Ptr LLVM.Module


structure State where
  var2val: Std.HashMap VarId (LLVM.Ptr LLVM.Value)
  -- arg2val: Std.HashMap Arg (LLVM.Ptr LLVM.Value)

-- def State.createInitStateIO (modName: Name): IO State := do
--   let ctx ← LLVM.createContext
--   let module ← LLVM.createModule ctx modName.toString -- TODO: pass module name
--   return { ctx := ctx, module := module : State }

inductive Error where
| unknownDeclaration: Name → Error
| invalidExportName: Name → Error
| unimplemented: String → Error
| compileError: String → Error -- TODO: these gotta be changed into real errors

instance : ToString Error where
  toString e := match e with
   | .unknownDeclaration n => s!"unknown declaration '{n}'"
   | .invalidExportName n => s!"invalid export name '{n}'"
   | .unimplemented s => s!"unimplemented '{s}'"
   | .compileError s => s!"compile eror '{s}'"


abbrev M := StateT State (ReaderT Context (ExceptT Error IO))


def addVartoState (x: VarId) (v: LLVM.Ptr LLVM.Value): M Unit :=
  modify (fun s => { s with var2val := s.var2val.insert x v}) -- add new variable


/-
def getEnv : M Environment := Context.env <$> read
def getModName : M Name := Context.modName <$> read
def getDecl (n : Name) : M Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => throw s!"unknown declaration '{n}'"
-/
def getLLVMContext : M (LLVM.Ptr LLVM.Context) := Context.llvmctx <$> read
def getLLVMModule : M (LLVM.Ptr LLVM.Module) := Context.llvmmodule <$> read
def getEnv : M Environment := Context.env <$> read
def getModName : M Name := Context.modName <$> read
def getDecl (n : Name) : M Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => IO.eprintln "getDecl failed!"; throw (Error.unknownDeclaration n)


-- vv emitMainFnIfIneeded vv
def getOrCreateFunctionPrototype (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module)
  (retty: LLVM.Ptr LLVM.LLVMType) (name: String) (args: Array (LLVM.Ptr LLVM.LLVMType)): M (LLVM.Ptr LLVM.Value) := do
  -- void lean_initialize();
  LLVM.getOrAddFunction mod name $
     (← LLVM.functionType retty args (isVarArg := false))


def getOrCreateLeanBoxFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidPtrType ctx) "lean_box"  #[(← LLVM.size_tTypeInContext ctx)]

def callLeanBox (builder: LLVM.Ptr LLVM.Builder) (arg: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanBoxFn) #[arg] name

def getOrCreateLeanIOMkWorldFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- lean_object* lean_io_mk_world();
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidPtrType ctx) "lean_io_mk_world"  #[]

def callLeanIOMkWorld (builder: LLVM.Ptr LLVM.Builder): M (LLVM.Ptr LLVM.Value) := do
   LLVM.buildCall builder (← getOrCreateLeanIOMkWorldFn (← getLLVMContext) (← getLLVMModule)) #[] "mk_io_out"


def getOrCreateLeanIOResultIsErrorFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- bool lean_io_result_is_err();
  getOrCreateFunctionPrototype ctx mod (← LLVM.i1Type ctx) "lean_io_result_is_error"  #[(← LLVM.voidPtrType ctx)]

def callLeanIOResultIsError (builder: LLVM.Ptr LLVM.Builder) (arg: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanIOResultIsErrorFn (← getLLVMContext) (← getLLVMModule)) #[arg] name

-- lean_alloc_ctor (unsigned tag, unsigned num_obj, unsigned scalar_sz)
def getOrCreateLeanAllocCtorFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let unsigned ← LLVM.size_tTypeInContext ctx
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidPtrType ctx) "lean_alloc_ctor"  #[unsigned, unsigned, unsigned]

def callLeanAllocCtor (builder: LLVM.Ptr LLVM.Builder) (tag num_objs scalar_sz: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanAllocCtorFn) #[tag, num_objs, scalar_sz] name

-- void lean_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v)
def getOrCreateLeanCtorSetFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let unsigned ← LLVM.size_tTypeInContext ctx
  let voidptr ← LLVM.voidPtrType ctx
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidTypeInContext ctx) "lean_ctor_set"  #[voidptr, unsigned, voidptr]

def callLeanCtorSet (builder: LLVM.Ptr LLVM.Builder) (o i v: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanCtorSetFn) #[o, i, v] name


-- lean_obj_res io_result_mk_ok(lean_obj_arg a)
def getOrCreateLeanIOResultMkOkFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let voidptr ← LLVM.voidPtrType ctx
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    voidptr "lean_io_result_mk_ok"  #[voidptr]

def callLeanIOResultMKOk (builder: LLVM.Ptr LLVM.Builder) (v: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanIOResultMkOkFn) #[v] name



/-
def toCType : IRType → String
  | IRType.float      => "double"
  | IRType.uint8      => "uint8_t"
  | IRType.uint16     => "uint16_t"
  | IRType.uint32     => "uint32_t"
  | IRType.uint64     => "uint64_t"
  | IRType.usize      => "size_t"
  | IRType.object     => "lean_object*"
  | IRType.tobject    => "lean_object*"
  | IRType.irrelevant => "lean_object*"
  | IRType.struct _ _ => panic! "not implemented yet"
  | IRType.union _ _  => panic! "not implemented yet"
-/
def toLLVMType (ctx: LLVM.Ptr LLVM.Context): IRType → IO (LLVM.Ptr LLVM.LLVMType)
  | IRType.float      => LLVM.doubleTypeInContext ctx
  | IRType.uint8      => LLVM.intTypeInContext ctx 8
  | IRType.uint16     => LLVM.intTypeInContext ctx 16
  | IRType.uint32     => LLVM.intTypeInContext ctx 32
  | IRType.uint64     => LLVM.intTypeInContext ctx 64
  -- TODO: how to cleanly size_t in LLVM? We can do eg. instantiate the current target and query for size.
  | IRType.usize      => LLVM.size_tTypeInContext ctx
  | IRType.object     => do LLVM.pointerType (← LLVM.i8Type ctx)
  | IRType.tobject    => do LLVM.pointerType (← LLVM.i8Type ctx)
  | IRType.irrelevant => do LLVM.pointerType (← LLVM.i8Type ctx)
  | IRType.struct _ _ => panic! "not implemented yet"
  | IRType.union _ _  => panic! "not implemented yet"


/-
def throwInvalidExportName {α : Type} (n : Name) : M α :=
  throw s!"invalid export name '{n}'"
-/
def throwInvalidExportName {α : Type} (n : Name) : M α := do
  IO.eprintln "invalid export Name!"; throw (Error.invalidExportName n)

/-
def toCName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => pure s
  | some _                   => throwInvalidExportName n
  | none                     => if n == `main then pure leanMainFn else pure n.mangle
-/
def toCName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => pure s
  | some _                   => throwInvalidExportName n
  | none                     => if n == `main then pure leanMainFn else pure n.mangle


-- vvvv LLVM UTILS vvvv

-- indicates whether the API for building the blocks for then/else should
-- forward the control flow to the merge block.
-- TODO: infer this automatically from the state of the basic block.
inductive ShouldForwardControlFlow where
| yes | no

-- build an if, and position the builder at the merge basic block after execution.
-- The '_' denotes that we return Unit on each branch.
-- TODO: get current function from the builder.
def buildIfThen_ (builder: LLVM.Ptr LLVM.Builder) (fn: LLVM.Ptr LLVM.Value)  (name: String) (brval: LLVM.Ptr LLVM.Value)
  (thencodegen: LLVM.Ptr LLVM.Builder → M ShouldForwardControlFlow): M Unit := do
  let builderBB ← LLVM.getInsertBlock builder
  let fn ← LLVM.getBasicBlockParent builderBB
  -- LLVM.positionBuilderAtEnd builder

  let nameThen := name ++ "Then"
  let nameElse := name ++ "Else"
  let nameMerge := name ++ "Merge"

  let thenbb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn nameThen
  let elsebb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn nameElse
  let mergebb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn nameMerge
  let _ ← LLVM.buildCondBr builder brval thenbb elsebb
  -- then
  LLVM.positionBuilderAtEnd builder thenbb
  let fwd? ← thencodegen builder
  LLVM.positionBuilderAtEnd builder thenbb
  match fwd? with
  | .yes => let _ ← LLVM.buildBr builder mergebb
  | .no => pure ()

  -- else
  LLVM.positionBuilderAtEnd builder elsebb
  let _ ← LLVM.buildBr builder mergebb
  -- merge
  LLVM.positionBuilderAtEnd builder mergebb

def buildIfThenElse_ (builder: LLVM.Ptr LLVM.Builder)  (name: String) (brval: LLVM.Ptr LLVM.Value)
  (thencodegen: LLVM.Ptr LLVM.Builder → M ShouldForwardControlFlow)
  (elsecodegen: LLVM.Ptr LLVM.Builder → M ShouldForwardControlFlow): M Unit := do
  let fn ← LLVM.getBasicBlockParent (← LLVM.getInsertBlock builder)
  -- LLVM.positionBuilderAtEnd builder insertpt
  let thenbb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn (name ++ "Then")
  let elsebb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn (name ++ "Else")
  let mergebb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn (name ++ "Merge")
  let _ ← LLVM.buildCondBr builder brval thenbb elsebb
  -- then
  LLVM.positionBuilderAtEnd builder thenbb
  let fwd? ← thencodegen builder
  LLVM.positionBuilderAtEnd builder thenbb
  match fwd? with
  | .yes => let _ ← LLVM.buildBr builder mergebb
  | .no => pure ()
  -- else
  LLVM.positionBuilderAtEnd builder elsebb
  let fwd? ← elsecodegen builder
  LLVM.positionBuilderAtEnd builder elsebb
  match fwd? with
  | .yes => let _ ← LLVM.buildBr builder mergebb
  | .no => pure ()
  -- merge
  LLVM.positionBuilderAtEnd builder mergebb

-- ^^^^ LLVM UTILS ^^^^

-- vvemitFnDeclsvv

/-
def emitFnDeclAux (decl : Decl) (cppBaseName : String) (isExternal : Bool) : M Unit := do
  let ps := decl.params
  let env ← getEnv
  if ps.isEmpty then
    if isClosedTermName env decl.name then emit "static "
    else if isExternal then emit "extern "
    else emit "LEAN_EXPORT "
  else
    if !isExternal then emit "LEAN_EXPORT "
  emit (toCType decl.resultType ++ " " ++ cppBaseName)
  unless ps.isEmpty do
    emit "("
    -- We omit irrelevant parameters for extern constants
    let ps := if isExternC env decl.name then ps.filter (fun p => !p.ty.isIrrelevant) else ps
    if ps.size > closureMaxArgs && isBoxedName decl.name then
      emit "lean_object**"
    else
      ps.size.forM fun i => do
        if i > 0 then emit ", "
        emit (toCType ps[i]!.ty)
    emit ")"
  emitLn ";"
-/

def emitFnDeclAux (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module)
  (decl : Decl) (cppBaseName : String) (isExternal : Bool) : M (LLVM.Ptr LLVM.Value) := do
  IO.println s!"\nvv\nemitFnDeclAux {decl}\n^^"
  -- let types : Array LLVM.LLVMType ← decl.params.mapM (toLLVMType ctx)
  let ps := decl.params
  let env ← getEnv
  -- if ps.isEmpty then
  --   if isClosedTermName env decl.name then emit "static "
  --   else if isExternal then emit "extern "
  --   else emit "LEAN_EXPORT "
  -- else
  --   if !isExternal then emit "LEAN_EXPORT "
  -- emit (toCType decl.resultType ++ " " ++ cppBaseName)
  IO.eprintln s!"creating result type ({decl.resultType})"
  let retty ← (toLLVMType ctx decl.resultType)
  IO.eprintln s!"...created!"
  let mut argtys := #[]
  for p in ps do
    -- if it is extern, then we must not add irrelevant args
    if !(isExternC env decl.name) || !p.ty.isIrrelevant then
      IO.eprintln s!"adding argument of type {p.ty}"
      argtys := argtys.push (← toLLVMType ctx p.ty)
      IO.eprintln "...added argument!"
  -- QUESTION: why do we care if it is boxed?
  if argtys.size > closureMaxArgs && isBoxedName decl.name then
    argtys := #[(← LLVM.voidPtrType ctx)]
  IO.eprintln "creating function type..."
  let fnty ← LLVM.functionType retty argtys (isVarArg := false)
  IO.eprintln "created function type!"
  LLVM.getOrAddFunction mod cppBaseName fnty
  -- unless ps.isEmpty do
  --   emit "("
  --   -- We omit irrelevant parameters for extern constants
  --   let ps := if isExternC env decl.name then ps.filter (fun p => !p.ty.isIrrelevant) else ps
  --   if ps.size > closureMaxArgs && isBoxedName decl.name then
  --     emit "lean_object**"
  --   else
  --     ps.size.forM fun i => do
  --       if i > 0 then emit ", "
  --       emit (toCType ps[i]!.ty)
  --   emit ")"
  -- emitLn ";"


/-
def emitFnDecl (decl : Decl) (isExternal : Bool) : M Unit := do
  let cppBaseName ← toCName decl.name
  emitFnDeclAux decl cppBaseName isExternal
-/

def emitFnDecl (decl : Decl) (isExternal : Bool) : M Unit := do
  let cppBaseName ← toCName decl.name
  let _ ← emitFnDeclAux (← getLLVMContext) (← getLLVMModule) decl cppBaseName isExternal

/-
def emitExternDeclAux (decl : Decl) (cNameStr : String) : M Unit := do
  let env ← getEnv
  let extC := isExternC env decl.name
  emitFnDeclAux decl cNameStr extC
-/
def emitExternDeclAux (decl : Decl) (cNameStr : String) : M Unit := do
  let env ← getEnv
  let extC := isExternC env decl.name
  let _ ← emitFnDeclAux (← getLLVMContext) (← getLLVMModule) decl cNameStr extC
/-
def emitFnDecls : M Unit := do
  let env ← getEnv
  let decls := getDecls env
  let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {}
  let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {}
  let usedDecls := usedDecls.toList
  usedDecls.forM fun n => do
    let decl ← getDecl n;
    match getExternNameFor env `c decl.name with
    | some cName => emitExternDeclAux decl cName
    | none       => emitFnDecl decl (!modDecls.contains n)
-/
def emitFnDecls : M Unit := do
  let env ← getEnv
  let decls := getDecls env
  let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {}
  let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {}
  let usedDecls := usedDecls.toList
  for n in usedDecls do
    let decl ← getDecl n;
    IO.println s!"processing {decl}"
    match getExternNameFor env `c decl.name with
    | some cName => emitExternDeclAux decl cName
    | none       => emitFnDecl decl (!modDecls.contains n)
  return ()

-- ^^emitFnDecls^^^

-- vvv emitFileHeader vvv


/-
def emitFileHeader : M Unit := do
  let env ← getEnv
  let modName ← getModName
  emitLn "// Lean compiler output"
  emitLn ("// Module: " ++ toString modName)
  emit "// Imports:"
  env.imports.forM fun m => emit (" " ++ toString m)
  emitLn ""
  emitLn "#include <lean/lean.h>"
  emitLns [
    "#if defined(__clang__)",
    "#pragma clang diagnostic ignored \"-Wunused-parameter\"",
    "#pragma clang diagnostic ignored \"-Wunused-label\"",
    "#elif defined(__GNUC__) && !defined(__CLANG__)",
    "#pragma GCC diagnostic ignored \"-Wunused-parameter\"",
    "#pragma GCC diagnostic ignored \"-Wunused-label\"",
    "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"",
    "#endif",
    "#ifdef __cplusplus",
    "extern \"C\" {",
    "#endif"
  ]
-/

def emitFileHeader : M Unit := return () -- this is purely C++ ceremony
-- ^^^ emitFileHeader^^^


-- vvvemitFnsvvv


def emitTailCall (v : Expr) : M Unit :=
  match v with
  | Expr.fap _ ys => do
    let ctx ← read
    let ps := ctx.mainParams
    unless ps.size == ys.size do throw (Error.compileError "invalid tail call")
    throw (Error.unimplemented "emitTailCall")
    /-
    if overwriteParam ps ys then
      emitLn "{"
      ps.size.forM fun i => do
        let p := ps[i]!
        let y := ys[i]!
        unless paramEqArg p y do
          emit (toCType p.ty); emit " _tmp_"; emit i; emit " = "; emitArg y; emitLn ";"
      ps.size.forM fun i => do
        let p := ps[i]!
        let y := ys[i]!
        unless paramEqArg p y do emit p.x; emit " = _tmp_"; emit i; emitLn ";"
      emitLn "}"
    else
      ys.size.forM fun i => do
        let p := ps[i]!
        let y := ys[i]!
        unless paramEqArg p y do emit p.x; emit " = "; emitArg y; emitLn ";"
    emitLn "goto _start;"
    -/
  | _ => throw (Error.compileError "bug at emitTailCall")


-- vvv emitVDecl.emitCtor
-- TODO: think if I need to actually load the value from the slot here.
def emitLhs (x: VarId): M (LLVM.Ptr LLVM.Value) := do
  let state ← get
  match state.var2val.find? x with
  | .some v => return v
  | .none => throw (Error.compileError s!"unable to find variable {x}")

/-
def argToCString (x : Arg) : String :=
  match x with
  | Arg.var x => toString x
  | _         => "lean_box(0)"

def emitArg (x : Arg) : M Unit :=
  emit (argToCString x)
-/
def emitArg (builder: LLVM.Ptr LLVM.Builder) (x : Arg) : M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  match x with
  | Arg.var x => emitLhs x
  | _ => do
    let slot ← LLVM.buildAlloca builder (← LLVM.voidPtrType ctx) "irrelevant_slot"
    let v ← callLeanBox builder (← LLVM.constIntUnsigned ctx 0) "irrelevant_val"
    let _ ← LLVM.buildStore builder v slot
    return slot
/-
def emitCtorScalarSize (usize : Nat) (ssize : Nat) : M Unit := do
  if usize == 0 then emit ssize
  else if ssize == 0 then emit "sizeof(size_t)*"; emit usize
  else emit "sizeof(size_t)*"; emit usize; emit " + "; emit ssize
-/

/-
def emitAllocCtor (c : CtorInfo) : M Unit := do
  emit "lean_alloc_ctor("; emit c.cidx; emit ", "; emit c.size; emit ", "
  emitCtorScalarSize c.usize c.ssize; emitLn ");"
-/
def emitAllocCtor (builder: LLVM.Ptr LLVM.Builder) (c : CtorInfo) : M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  -- throw (Error.unimplemented "emitAllocCtor")
  let scalarSize := 900; -- HACK: do find the correct size.
  let idx ← LLVM.constIntUnsigned ctx (UInt64.ofNat c.cidx)
  let n ← LLVM.constIntUnsigned ctx (UInt64.ofNat c.size)
  let scalarSize ← LLVM.constIntUnsigned ctx (UInt64.ofNat scalarSize)
  callLeanAllocCtor builder idx n scalarSize "lean_alloc_ctor_out"
/-
def emitCtorSetArgs (z : VarId) (ys : Array Arg) : M Unit :=
  ys.size.forM fun i => do
    emit "lean_ctor_set("; emit z; emit ", "; emit i; emit ", "; emitArg ys[i]!; emitLn ");"
-/
def emitCtorSetArgs (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (ys : Array Arg) : M Unit := do
  IO.eprintln "##-1##"
  ys.size.forM fun i => do
    -- -- emit "lean_ctor_set("; emit z; emit ", "; emit i; emit ", "; emitArg ys[i]!; emitLn ");"
    IO.println "#######0#######"
    let zslot ← emitLhs z;
    let zv ← LLVM.buildLoad builder zslot "z"
    -- IO.eprintln "##1##"
    let yslot ← emitArg builder ys[i]!
    let yv ← LLVM.buildLoad builder yslot "y"
    -- IO.eprintln "##2##"
    let iv ← LLVM.constIntUnsigned (← getLLVMContext) (UInt64.ofNat i)
    IO.eprintln "######3#######"
    let _ ← callLeanCtorSet builder zv iv yv ""
    IO.eprintln "######4#######"
    let _ ← LLVM.buildStore builder zv zslot
    IO.eprintln "######45#######"
    pure ()
/-
def emitCtor (z : VarId) (c : CtorInfo) (ys : Array Arg) : M Unit := do
  emitLhs z;
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    emit "lean_box("; emit c.cidx; emitLn ");"
  else do
    emitAllocCtor c; emitCtorSetArgs z ys
-/
def emitCtor (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (c : CtorInfo) (ys : Array Arg) : M Unit := do
  let slot ← emitLhs z;
  addVartoState z slot

  let ctx ← getLLVMContext
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    let v ← callLeanBox builder (← LLVM.constInt (← LLVM.size_tTypeInContext ctx) 0) "lean_box_outv"
    let _ ← LLVM.buildStore builder v slot
  else do
    let v ← emitAllocCtor builder c;
    emitCtorSetArgs builder z ys -- TODO:
    IO.eprintln "######5#######"
    let _ ← LLVM.buildStore builder v slot


-- ^^^ emitVDecl.emitCtor
/-
def emitVDecl (z : VarId) (t : IRType) (v : Expr) : M Unit :=
  match v with
  | Expr.ctor c ys      => emitCtor z c ys
  | Expr.reset n x      => emitReset z n x
  | Expr.reuse x c u ys => emitReuse z x c u ys
  | Expr.proj i x       => emitProj z i x
  | Expr.uproj i x      => emitUProj z i x
  | Expr.sproj n o x    => emitSProj z t n o x
  | Expr.fap c ys       => emitFullApp z c ys
  | Expr.pap c ys       => emitPartialApp z c ys
  | Expr.ap x ys        => emitApp z x ys
  | Expr.box t x        => emitBox z x t
  | Expr.unbox x        => emitUnbox z t x
  | Expr.isShared x     => emitIsShared z x
  | Expr.isTaggedPtr x  => emitIsTaggedPtr z x
  | Expr.lit v          => emitLit z t v
-/
def emitVDecl (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (t : IRType) (v : Expr) : M Unit :=
  match v with
  | Expr.ctor c ys      => emitCtor builder z c ys -- throw (Error.unimplemented "emitCtor z c ys")
  | Expr.reset n x      => throw (Error.unimplemented "emitReset z n x")
  | Expr.reuse x c u ys => throw (Error.unimplemented "emitReuse z x c u ys")
  | Expr.proj i x       => throw (Error.unimplemented "emitProj z i x")
  | Expr.uproj i x      => throw (Error.unimplemented "emitUProj z i x")
  | Expr.sproj n o x    => throw (Error.unimplemented "emitSProj z t n o x")
  | Expr.fap c ys       => throw (Error.unimplemented "emitFullApp z c ys")
  | Expr.pap c ys       => throw (Error.unimplemented "emitPartialApp z c ys")
  | Expr.ap x ys        => throw (Error.unimplemented "emitApp z x ys")
  | Expr.box t x        => throw (Error.unimplemented "emitBox z x t")
  | Expr.unbox x        => throw (Error.unimplemented "emitUnbox z t x")
  | Expr.isShared x     => throw (Error.unimplemented "emitIsShared z x")
  | Expr.isTaggedPtr x  => throw (Error.unimplemented "emitIsTaggedPtr z x")
  | Expr.lit v          => throw (Error.unimplemented "emitLit z t v")


/-
def declareVar (x : VarId) (t : IRType) : M Unit := do
  emit (toCType t); emit " "; emit x; emit "; "
-/
def declareVar (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (t : IRType) : M Unit := do
  let alloca ← LLVM.buildAlloca builder (← toLLVMType (← getLLVMContext) t) "varx"
  addVartoState x alloca
  IO.eprintln s!"### declared {x} ###"
/-
partial def declareVars : FnBody → Bool → M Bool
  | e@(FnBody.vdecl x t _ b), d => do
    let ctx ← read
    if isTailCallTo ctx.mainFn e then
      pure d
    else
      declareVar x t; declareVars b true
  | FnBody.jdecl _ xs _ b,    d => do declareParams xs; declareVars b (d || xs.size > 0)
  | e,                        d => if e.isTerminal then pure d else declareVars e.body d
-/
partial def declareVars (builder: LLVM.Ptr LLVM.Builder): FnBody → M Unit
  | e@(FnBody.vdecl x t _ b) => do
    let ctx ← read
    /-
    if isTailCallTo ctx.mainFn e then
      pure d
    else
      declareVar x t; declareVars b true
    -/
    declareVar builder x t; declareVars builder b

  | FnBody.jdecl _ xs _ b => do
      throw (Error.unimplemented "declareVars.jdecl")
      -- do declareParams xs; declareVars b (d || xs.size > 0)
  | e => do
      if e.isTerminal then pure () else declareVars builder e.body


/-
mutual
-/
mutual

/-
partial def emitIf (x : VarId) (xType : IRType) (tag : Nat) (t : FnBody) (e : FnBody) : M Unit := do
  emit "if ("; emitTag x xType; emit " == "; emit tag; emitLn ")";
  emitFnBody t;
  emitLn "else";
  emitFnBody e
-/

/-
partial def emitCase (x : VarId) (xType : IRType) (alts : Array Alt) : M Unit :=
  match isIf alts with
  | some (tag, t, e) => emitIf x xType tag t e
  | _ => do
    emit "switch ("; emitTag x xType; emitLn ") {";
    let alts := ensureHasDefault alts;
    alts.forM fun alt => do
      match alt with
      | Alt.ctor c b  => emit "case "; emit c.cidx; emitLn ":"; emitFnBody b
      | Alt.default b => emitLn "default: "; emitFnBody b
    emitLn "}"
-/
/-
partial def emitBlock (b : FnBody) : M Unit := do
  match b with
  | FnBody.jdecl _ _  _ b      => emitBlock b
  | d@(FnBody.vdecl x t v b)   =>
    let ctx ← read
    if isTailCallTo ctx.mainFn d then
      emitTailCall v
    else
      emitVDecl x t v
      emitBlock b
  | FnBody.inc x n c p b       =>
    unless p do emitInc x n c
    emitBlock b
  | FnBody.dec x n c p b       =>
    unless p do emitDec x n c
    emitBlock b
  | FnBody.del x b             => emitDel x; emitBlock b
  | FnBody.setTag x i b        => emitSetTag x i; emitBlock b
  | FnBody.set x i y b         => emitSet x i y; emitBlock b
  | FnBody.uset x i y b        => emitUSet x i y; emitBlock b
  | FnBody.sset x i o y t b    => emitSSet x i o y t; emitBlock b
  | FnBody.mdata _ b           => emitBlock b
  | FnBody.ret x               => emit "return "; emitArg x; emitLn ";"
  | FnBody.case _ x xType alts => emitCase x xType alts
  | FnBody.jmp j xs            => emitJmp j xs
  | FnBody.unreachable         => emitLn "lean_internal_panic_unreachable();"
-/

partial def emitBlock (builder: LLVM.Ptr LLVM.Builder) (b : FnBody) : M Unit := do
  match b with
  | FnBody.jdecl _ _  _ b      =>  throw (Error.unimplemented "join points are unimplemented")
       --emitBlock b
  | d@(FnBody.vdecl x t v b)   => do
    -- throw (Error.unimplemented "vdecl")
    let ctx ← read
    if isTailCallTo ctx.mainFn d then
      emitTailCall v
    else
      emitVDecl builder x t v
      emitBlock builder b
  | FnBody.inc x n c p b       => throw (Error.unimplemented "inc")
  /-
    unless p do emitInc x n c
    emitBlock b
  -/
  | FnBody.dec x n c p b       => throw (Error.unimplemented "dec")
  /-
    unless p do emitDec x n c
    emitBlock b
  -/
  | FnBody.del x b             => throw (Error.unimplemented "del")
  /-
  emitDel x; emitBlock b
  -/
  | FnBody.setTag x i b        => throw (Error.unimplemented "setTag")
  /-
  emitSetTag x i; emitBlock b
  -/
  | FnBody.set x i y b         => throw (Error.unimplemented "set")
  /-
  emitSet x i y; emitBlock b
  -/
  | FnBody.uset x i y b        => throw (Error.unimplemented "uset")
  /-
  emitUSet x i y; emitBlock b
  -/
  | FnBody.sset x i o y t b    => throw (Error.unimplemented "sset")
  /-
  emitSSet x i o y t; emitBlock b
  -/
  | FnBody.mdata _ b           =>  throw (Error.unimplemented "mdata")
  /-
  emitBlock b
  -/
  | FnBody.ret x               => do
      /-
      emit "return "; emitArg x; emitLn ";"
      -/
      let xslot ← emitArg builder x
      let xv ← LLVM.buildLoad builder xslot "ret_val"
      let _ ← LLVM.buildRet builder xv
  | FnBody.case _ x xType alts => throw (Error.unimplemented "case")
  /- emitCase x xType alts
  -/
  | FnBody.jmp j xs            => throw (Error.unimplemented "jump")
  /-
  emitJmp j xs
  -/
  | FnBody.unreachable         => throw (Error.unimplemented "unreachable")
  /-
  emitLn "lean_internal_panic_unreachable();"
  -/

/-
partial def emitJPs : FnBody → M Unit
  | FnBody.jdecl j _  v b => do emit j; emitLn ":"; emitFnBody v; emitJPs b
  | e                     => do unless e.isTerminal do emitJPs e.body
-/


/-
partial def emitFnBody (b : FnBody) : M Unit := do
  emitLn "{"
  let declared ← declareVars b false
  if declared then emitLn ""
  emitBlock b
  emitJPs b
  emitLn "}"
-/
partial def emitFnBody (llvmctx: LLVM.Ptr LLVM.Context) (b : FnBody) (llvmfn: LLVM.Ptr LLVM.Value) (builder: LLVM.Ptr LLVM.Builder): M Unit := do

  -- let declared ← declareVars b false
  -- if declared then emitLn ""
  declareVars builder b

  -- emitLn "{"
  emitBlock builder b   -- emitBlock b
  -- LLVM.positionBuilderAtEnd builder bb

  -- emitJPs b
  -- emitLn "}"

/-
end
-/
end



/-
def emitDeclAux (d : Decl) : M Unit := do
  let env ← getEnv
  let (_, jpMap) := mkVarJPMaps d
  withReader (fun ctx => { ctx with jpMap := jpMap }) do
  unless hasInitAttr env d.name do
    match d with
    | .fdecl (f := f) (xs := xs) (type := t) (body := b) .. =>
      let baseName ← toCName f;
      if xs.size == 0 then
        emit "static "
      else
        emit "LEAN_EXPORT "  -- make symbol visible to the interpreter
      emit (toCType t); emit " ";
      if xs.size > 0 then
        emit baseName;
        emit "(";
        if xs.size > closureMaxArgs && isBoxedName d.name then
          emit "lean_object** _args"
        else
          xs.size.forM fun i => do
            if i > 0 then emit ", "
            let x := xs[i]!
            emit (toCType x.ty); emit " "; emit x.x
        emit ")"
      else
        emit ("_init_" ++ baseName ++ "()")
      emitLn " {";
      if xs.size > closureMaxArgs && isBoxedName d.name then
        xs.size.forM fun i => do
          let x := xs[i]!
          emit "lean_object* "; emit x.x; emit " = _args["; emit i; emitLn "];"
      emitLn "_start:";
      withReader (fun ctx => { ctx with mainFn := f, mainParams := xs }) (emitFnBody b);
      emitLn "}"
    | _ => pure ()
-/


def emitFnArgs (ctx: LLVM.Ptr LLVM.Context) (builder: LLVM.Ptr LLVM.Builder) (llvmfn: LLVM.Ptr LLVM.Value) (params: Array Param) : M Unit := do
  let n := LLVM.countParams llvmfn
  for i in (List.range n.toNat) do
    let alloca ← LLVM.buildAlloca builder (← toLLVMType (← getLLVMContext) params[i]!.ty) ("arg_" ++ toString i)
    let arg ← LLVM.getParam llvmfn (UInt64.ofNat i)
    let _ ← LLVM.buildStore builder arg alloca
    addVartoState params[i]!.x alloca

-- TODO: figure out if we can always return the corresponding function?
def emitDeclAux (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module) (builder: LLVM.Ptr LLVM.Builder) (d : Decl): M Unit := do
  IO.println "vvvv\nemitDeclAux {d}\n^^^\n"
  let env ← getEnv
  let (_, jpMap) := mkVarJPMaps d
  withReader (fun ctx => { ctx with jpMap := jpMap }) do
  unless hasInitAttr env d.name do
    match d with
    | .fdecl (f := f) (xs := xs) (type := t) (body := b) .. =>
      let baseName ← toCName f;
      -- if xs.size == 0 then
      --   emit "static "
      -- else
      --   emit "LEAN_EXPORT "  -- make symbol visible to the interpreter
      --create initializer for closed terms.
      let name := if xs.size > 0 then baseName else "_init_" ++ baseName
      let retty ← toLLVMType ctx t
      let mut argtys := #[]
      if xs.size > closureMaxArgs && isBoxedName d.name then
        argtys := #[(← LLVM.voidPtrType ctx)]
      else
        for x in xs do
          argtys := argtys.push (← toLLVMType ctx x.ty)
      let fnty ← LLVM.functionType retty argtys (isVarArg := false)
      let llvmfn ← LLVM.getOrAddFunction mod name fnty
      -- emit (toCType t); emit " ";
      -- if xs.size > 0 then
      --   emit baseName;
      --   emit "(";
      --   if xs.size > closureMaxArgs && isBoxedName d.name then
      --     emit "lean_object** _args"
      --   else
      --     xs.size.forM fun i => do
      --       if i > 0 then emit ", "
      --       let x := xs[i]!
      --       emit (toCType x.ty); emit " "; emit x.x
      --   emit ")"
      -- else
      --   emit ("_init_" ++ baseName ++ "()")
      -- emitLn " {";
      if xs.size > closureMaxArgs && isBoxedName d.name then
        throw (Error.unimplemented "unimplemented > closureMaxArgs case")
      --   xs.size.forM fun i => do
      --     let x := xs[i]!
      --     emit "lean_object* "; emit x.x; emit " = _args["; emit i; emitLn "];"
      -- emitLn "_start:";
      withReader (fun ctx => { ctx with mainFn := f, mainParams := xs }) (do
        set { var2val := default : EmitLLVM.State } -- flush varuable map
        let bb ← LLVM.appendBasicBlockInContext (← getLLVMContext) llvmfn "entry"
        LLVM.positionBuilderAtEnd builder bb
        emitFnArgs ctx builder llvmfn xs
        emitFnBody ctx b llvmfn builder);
      -- emitLn "}"
      pure ()
    | _ => pure ()

/-
def emitDecl (d : Decl) : M Unit := do
  let d := d.normalizeIds; -- ensure we don't have gaps in the variable indices
  try
    emitDeclAux d
  catch err =>
    throw s!"{err}\ncompiling:\n{d}"
-/

def emitDecl (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module) (builder: LLVM.Ptr LLVM.Builder) (d : Decl) : M Unit := do
  IO.eprintln s!"vvv\nemitDecl\n{d}\n^^^\n"
  let d := d.normalizeIds; -- ensure we don't have gaps in the variable indices
  try
    emitDeclAux ctx mod builder d
    return ()
  catch err =>
    throw (Error.unimplemented s!"{err}\ncompiling:\n{d}")

/-
def emitFns : M Unit := do
  let env ← getEnv;
  let decls := getDecls env;
  decls.reverse.forM emitDecl
-/

def emitFns (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module) (builder: LLVM.Ptr LLVM.Builder) : M Unit := do
  let env ← getEnv
  let decls := getDecls env;
  IO.eprintln "gotten decls, going to loop..."
  decls.reverse.forM (emitDecl ctx mod builder)
-- ^^^ emitFns ^^^

-- vv emitInitFn vv
/-
def emitMarkPersistent (d : Decl) (n : Name) : M Unit := do
  if d.resultType.isObj then
    emit "lean_mark_persistent("
    emitCName n
    emitLn ");"
-/

/-
def emitDeclInit (d : Decl) : M Unit := do
  let env ← getEnv
  let n := d.name
  if isIOUnitInitFn env n then
    emit "res = "; emitCName n; emitLn "(lean_io_mk_world());"
    emitLn "if (lean_io_result_is_error(res)) return res;"
    emitLn "lean_dec_ref(res);"
  else if d.params.size == 0 then
    match getInitFnNameFor? env d.name with
    | some initFn =>
      if getBuiltinInitFnNameFor? env d.name |>.isSome then
        emit "if (builtin) {"
      emit "res = "; emitCName initFn; emitLn "(lean_io_mk_world());"
      emitLn "if (lean_io_result_is_error(res)) return res;"
      emitCName n; emitLn " = lean_io_result_get_value(res);"
      emitMarkPersistent d n
      emitLn "lean_dec_ref(res);"
      if getBuiltinInitFnNameFor? env d.name |>.isSome then
        emit "}"
    | _ =>
      emitCName n; emit " = "; emitCInitName n; emitLn "();"; emitMarkPersistent d n
-/

def emitDeclInit (builder: LLVM.Ptr LLVM.Builder) (parentFn: LLVM.Ptr LLVM.Value) (d : Decl) : M Unit := do
  let env ← getEnv
  let n := d.name
  if isIOUnitInitFn env n then do
    -- emit "res = "; emitCName n; emitLn "(lean_io_mk_world());"
    -- emitLn "if (lean_io_result_is_error(res)) return res;"
    -- emitLn "lean_dec_ref(res);"
    let res ← callLeanIOMkWorld builder
    let err? ← callLeanIOResultIsError builder res "is_error"
    buildIfThen_ builder parentFn "IsError" err?
      (fun builder => do
        let _ ← LLVM.buildRet builder res
        pure ShouldForwardControlFlow.no)
    -- TODO: emit lean_dec_ref. For now, it does not matter.
  else if d.params.size == 0 then
    match getInitFnNameFor? env d.name with
    | some initFn =>
      if getBuiltinInitFnNameFor? env d.name |>.isSome then

      /-
        emit "if (builtin) {"
      emit "res = "; emitCName initFn; emitLn "(lean_io_mk_world());"
      emitLn "if (lean_io_result_is_error(res)) return res;"
      emitCName n; emitLn " = lean_io_result_get_value(res);"
      emitMarkPersistent d n
      emitLn "lean_dec_ref(res);"
      if getBuiltinInitFnNameFor? env d.name |>.isSome then
        emit "}"
      -/
        throw (Error.unimplemented "unimplemented emitDeclInit [d.params.size == 0]")
    | _ =>
      throw (Error.unimplemented "emitMarkPersistent")
      -- emitCName n; emit " = "; emitCInitName n; emitLn "();"; emitMarkPersistent d n

def emitInitFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module) (builder: LLVM.Ptr LLVM.Builder): M Unit := do
  let env ← getEnv
  let modName ← getModName

  let initFnTy ← LLVM.functionType (← LLVM.voidPtrType ctx) #[ (← LLVM.i8Type ctx), (← LLVM.voidPtrType ctx)] (isVarArg := false)
  let initFn ← LLVM.getOrAddFunction mod (mkModuleInitializationFunctionName modName) initFnTy
  let entryBB ← LLVM.appendBasicBlockInContext ctx initFn "entry"
  LLVM.positionBuilderAtEnd builder entryBB
      /-
    emitLns [
      "static bool _G_initialized = false;",
      "LEAN_EXPORT lean_object* " ++ mkModuleInitializationFunctionName modName ++ "(uint8_t builtin, lean_object* w) {",
      "lean_object * res;",
      "if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));",
      "_G_initialized = true;"
    ]
    -/
  let ginitslot ← LLVM.getOrAddGlobal mod (modName.mangle ++ "_G_initialized") (← LLVM.i1Type ctx)
  LLVM.setInitializer ginitslot (← LLVM.False ctx)
  let ginitv ← LLVM.buildLoad builder ginitslot "init_v"
  buildIfThen_ builder initFn "isGInitialized" ginitv
    (fun builder => do
      let box0 ← callLeanBox builder (← LLVM.constIntUnsigned ctx 0) "box0"
      let out ← callLeanIOResultMKOk builder box0 "retval"
      let _ ← LLVM.buildRet builder out
      pure ShouldForwardControlFlow.no)
  LLVM.buildStore builder (← LLVM.True ctx) ginitslot

  /-
  env.imports.forM fun imp => emitLns [
    "res = " ++ mkModuleInitializationFunctionName imp.module ++ "(builtin, lean_io_mk_world());",
    "if (lean_io_result_is_error(res)) return res;",
    "lean_dec_ref(res);"]
  -/
  env.imports.forM fun import => do
    let importFnTy ← LLVM.functionType (← LLVM.voidPtrType ctx) #[ (← LLVM.i8Type ctx), (← LLVM.voidPtrType ctx)] (isVarArg := false)
    let importInitFn ← LLVM.getOrAddFunction mod (mkModuleInitializationFunctionName import.module) importFnTy
    let builtin ← LLVM.getParam initFn 0
    let world ← callLeanIOMkWorld builder
    let res ← LLVM.buildCall builder initFn #[builtin, world] ("res_" ++ import.module.mangle)
    let err? ← callLeanIOResultIsError builder res ("res_is_error_"  ++ import.module.mangle)
    buildIfThen_ builder initFn ("IsError" ++ import.module.mangle) err?
      (fun builder => do
        let _ ← LLVM.buildRet builder res
        pure ShouldForwardControlFlow.no)
    -- TODO: call lean_dec_ref. It's fine to not decrement refcounts.
    /-
    let decls := getDecls env
    decls.reverse.forM emitDeclInit
    -/
  -- emitLns ["return lean_io_result_mk_ok(lean_box(0));", "}"]
  let decls := getDecls env
  decls.reverse.forM (emitDeclInit builder initFn)
  let box0 ← callLeanBox builder (← LLVM.constIntUnsigned ctx 0) "box0"
  let out ← callLeanIOResultMKOk builder box0 "retval"
  let _ ← LLVM.buildRet builder out
-- ^^ emitInitFn ^^




def getOrCreateLeanInitialize (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- void lean_initialize();
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidTypeInContext ctx) "lean_initialize"  #[]

def getOrCreateLeanInitializeRuntimeModule (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- void lean_initialize();
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidTypeInContext ctx) "lean_initialize_runtime_module"  #[]

def getOrCreateLeanSetPanicMessages (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- void lean_set_panic_messages();
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidTypeInContext ctx) "lean_set_panic_messages"  #[(← LLVM.i1Type ctx)]


def getOrCreateLeanIOMarkEndInitializationFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- lean_object* lean_io_mk_world();
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidTypeInContext ctx) "lean_io_mark_end_initialization"  #[]

def getOrCreateLeanIOResultIsOkFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- lean_object* lean_io_mk_world();
  getOrCreateFunctionPrototype ctx mod (← LLVM.i1Type ctx) "lean_io_result_is_ok"  #[(← LLVM.voidPtrType ctx)]

def callLeanIOResultIsOk (builder: LLVM.Ptr LLVM.Builder) (arg: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanIOResultIsOkFn (← getLLVMContext) (← getLLVMModule)) #[arg] name


def getOrCreateLeanDecRefFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidTypeInContext ctx) "lean_dec_ref"  #[(← LLVM.i8PtrType ctx)]

def callLeanDecRef (builder: LLVM.Ptr LLVM.Builder) (res: LLVM.Ptr LLVM.Value): M Unit := do
   let _ ← LLVM.buildCall builder (← getOrCreateLeanDecRefFn) #[res] ""

def getOrCreateLeanInitTaskManagerFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidTypeInContext ctx) "lean_init_task_manager"  #[]


def callLeanInitTaskManager (builder: LLVM.Ptr LLVM.Builder): M Unit := do
   let _ ← LLVM.buildCall builder (← getOrCreateLeanInitTaskManagerFn) #[] "init_out"


def getOrCreateLeanFinalizeTaskManager: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidTypeInContext ctx) "lean_finalize_task_manager"  #[]


def callLeanFinalizeTaskManager (builder: LLVM.Ptr LLVM.Builder): M Unit := do
   let _ ← LLVM.buildCall builder (← getOrCreateLeanFinalizeTaskManager) #[] ""

def getOrCreateCallLeanUnboxUint32Fn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.i32Type ctx) "lean_unbox_uint32"  #[← LLVM.voidPtrType ctx]


def callLeanUnboxUint32 (builder: LLVM.Ptr LLVM.Builder) (v: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
   LLVM.buildCall builder (← getOrCreateCallLeanUnboxUint32Fn) #[v] name

def getOrCreateLeanIOResultGetValueFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidPtrType ctx) "lean_io_result_get_value"  #[← LLVM.voidPtrType ctx]

def callLeanIOResultGetValue (builder: LLVM.Ptr LLVM.Builder) (v: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
   LLVM.buildCall builder (← getOrCreateLeanIOResultGetValueFn) #[v] name



def getOrCreateLeanIOResultShowErrorFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidTypeInContext ctx) "lean_io_result_show_error"  #[← LLVM.voidPtrType ctx]

def callLeanIOResultShowError (builder: LLVM.Ptr LLVM.Builder) (v: LLVM.Ptr LLVM.Value) (name: String): M Unit := do
   let _ ← LLVM.buildCall builder (← getOrCreateLeanIOResultShowErrorFn) #[v] name




def emitMainFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module) (builder: LLVM.Ptr LLVM.Builder): M Unit := do
  let d ← getDecl `main
  let xs ← match d with
   | .fdecl (xs := xs) .. => pure xs
   | _ =>  throw (Error.compileError "function declaration expected")

  unless xs.size == 2 || xs.size == 1 do throw (Error.compileError "invalid main function, incorrect arity when generating code")
  let env ← getEnv
  let usesLeanAPI := usesModuleFrom env `Lean
  /-
  if usesLeanAPI then
      emitLn "void lean_initialize();"
  else
      emitLn "void lean_initialize_runtime_module();";
  -/
  /-
  emitLn "
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
-/

  /-
  int main(int argc, char ** argv) {
  -/
  let mainTy ← LLVM.functionType (← LLVM.i64Type ctx) #[(← LLVM.i64Type ctx), (← LLVM.voidPtrType ctx)] (isVarArg := false)
  let main ← LLVM.getOrAddFunction mod "main" mainTy
  let entry ← LLVM.appendBasicBlockInContext ctx main "entry"
  LLVM.positionBuilderAtEnd builder entry
  /-
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  #endif
  -/
  /-
  lean_object* in; lean_object* res;";
  -/
  let in_ ← LLVM.buildAlloca builder (← LLVM.i8PtrType ctx) "in"
  let res ← LLVM.buildAlloca builder (← LLVM.i8PtrType ctx) "res"
  /-
  if usesLeanAPI then
    emitLn "lean_initialize();"
  else
    emitLn "lean_initialize_runtime_module();"
  -/
  let initfn ← if usesLeanAPI then getOrCreateLeanInitialize ctx mod else getOrCreateLeanInitializeRuntimeModule ctx mod
  let _ ← LLVM.buildCall builder initfn #[] ""
  let modName ← getModName
    /- We disable panic messages because they do not mesh well with extracted closed terms.
        See issue #534. We can remove this workaround after we implement issue #467. -/
    /-
    emitLn "lean_set_panic_messages(false);"
    emitLn ("res = " ++ mkModuleInitializationFunctionName modName ++ "(1 /* builtin */, lean_io_mk_world());")
    emitLn "lean_set_panic_messages(true);"
    emitLns ["lean_io_mark_end_initialization();",
              "if (lean_io_result_is_ok(res)) {",
              "lean_dec_ref(res);",
              "lean_init_task_manager();"];
    -/
  let setPanicMesagesFn ← getOrCreateLeanSetPanicMessages ctx mod
  -- | TODO: remove reuse of the same function type across two locations
  let modInitFnTy ← LLVM.functionType (← LLVM.voidPtrType ctx) #[ (← LLVM.i8Type ctx), (← LLVM.voidPtrType ctx)] (isVarArg := false)
  let modInitFn ← LLVM.getOrAddFunction mod (mkModuleInitializationFunctionName modName) modInitFnTy
  let _ ← LLVM.buildCall builder setPanicMesagesFn #[(← LLVM.False ctx )] ""
  let world ← LLVM.buildCall builder (← getOrCreateLeanIOMkWorldFn ctx mod) #[] "world"

  let resv ← LLVM.buildCall builder modInitFn #[(← LLVM.constInt8 ctx 1 ), world] (modName.toString ++ "init_out")
  let _ ← LLVM.buildStore builder resv res

  let _ ← LLVM.buildCall builder setPanicMesagesFn #[(← LLVM.True ctx )] ""
  let _ ← LLVM.buildCall builder (← getOrCreateLeanIOMarkEndInitializationFn ctx mod) #[] ""

  let resv ← LLVM.buildLoad builder res "resv"
  let res_is_ok ← callLeanIOResultIsOk builder resv "res_is_ok"
  buildIfThen_ builder main "resIsOkBranches"  res_is_ok
    (fun builder => do -- then clause of the builder)
      if xs.size == 2 then
        callLeanDecRef builder res;
        callLeanInitTaskManager builder;
        let inv ← callLeanBox builder (← LLVM.constInt (← LLVM.size_tTypeInContext ctx) 0) "inv"
        let _ ← LLVM.buildStore builder inv in_
        -- TODO: have yet to do the while loop!
        -- TODO: have yet to do the while loop!
        -- TODO: have yet to do the while loop!

        /-
          emitLns ["in = lean_box(0);",
                    "int i = argc;",
                    "while (i > 1) {",
                    " lean_object* n;",
                    " i--;",
                    " n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);",
                    " in = n;",
                  "}"]
          -/
          /-
          emitLn ("res = " ++ leanMainFn ++ "(in, lean_io_mk_world());")
          -/
        let leanMainFnTy ← LLVM.functionType (← LLVM.voidPtrType ctx) #[(← LLVM.voidPtrType ctx), (← LLVM.voidPtrType ctx)]
        let leanMainFn ← LLVM.getOrAddFunction mod leanMainFn leanMainFnTy
        let world ← callLeanIOMkWorld builder
        let inv ← LLVM.buildLoad builder in_ "inv"
        let resv ← LLVM.buildCall builder leanMainFn #[inv, world] "resv"
        let _ ← LLVM.buildStore builder resv res
        pure ShouldForwardControlFlow.yes
      else
          /-
          emitLn ("res = " ++ leanMainFn ++ "(lean_io_mk_world());")
          -/
          let leanMainFnTy ← LLVM.functionType (← LLVM.voidPtrType ctx) #[(← LLVM.voidPtrType ctx)]
          let leanMainFn ← LLVM.getOrAddFunction mod leanMainFn leanMainFnTy
          let world ← callLeanIOMkWorld builder
          let resv ← LLVM.buildCall builder leanMainFn #[world] "resv"
          let _ ← LLVM.buildStore builder resv res
          pure ShouldForwardControlFlow.yes
    )

  -- `IO _`
  let retTy := env.find? `main |>.get! |>.type |>.getForallBody
  -- either `UInt32` or `(P)Unit`
  let retTy := retTy.appArg!
  -- finalize at least the task manager to avoid leak sanitizer false positives from tasks outliving the main thread
  let _ ← callLeanFinalizeTaskManager builder
  /-
  emitLns ["lean_finalize_task_manager();",
            "if (lean_io_result_is_ok(res)) {",
            "  int ret = " ++ if retTy.constName? == some ``UInt32 then "lean_unbox_uint32(lean_io_result_get_value(res));" else "0;",
            "  lean_dec_ref(res);",
            "  return ret;",
            "} else {",
            "  lean_io_result_show_error(res);",
            "  lean_dec_ref(res);",
            "  return 1;",
            "}"]
  -/
  -- emitLn "}"
  let resv ← LLVM.buildLoad builder res "resv"
  let res_is_ok ← callLeanIOResultIsOk builder resv "res_is_ok"
  buildIfThenElse_ builder "res.is.ok" res_is_ok
    (fun builder => -- then builder
      if retTy.constName? == some ``UInt32 then do
        let resv ← LLVM.buildLoad builder res "resv"
        let retv ← callLeanUnboxUint32 builder (← callLeanIOResultGetValue builder resv "io_val") "retv"
        let _ ← LLVM.buildRet builder retv
        pure ShouldForwardControlFlow.no
      else do
        let _ ← LLVM.buildRet builder (← LLVM.constInt64 ctx 0)
        pure ShouldForwardControlFlow.no

    )
    (fun builder => do -- else builder
        let resv ← LLVM.buildLoad builder res "resv"
        callLeanIOResultShowError builder resv ""
        callLeanDecRef builder resv
        let _ ← LLVM.buildRet builder (← LLVM.constInt64 ctx 0)
        pure ShouldForwardControlFlow.no)
  -- at the merge
  let _ ← LLVM.buildUnreachable builder




def hasMainFn : M Bool := do
  let env ← getEnv
  let decls := getDecls env
  return decls.any (fun d => d.name == `main)


def emitMainFnIfNeeded (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module) (builder: LLVM.Ptr LLVM.Builder): M Unit := do
  if (← hasMainFn) then emitMainFn ctx mod builder

-- ^^ emitMainFnIfNeeded ^^

-- vv EmitFileFooter vv
/-
def emitFileFooter : M Unit :=
  emitLns [
   "#ifdef __cplusplus",
   "}",
   "#endif"
  ]
-/

def emitFileFooter : M Unit := pure ()

-- ^^ emitFileFooter ^^
/-
def main : M Unit := do
  emitFileHeader
  emitFnDecls
  emitFns
  emitInitFn
  emitMainFnIfNeeded
  emitFileFooter
-/

def main : M Unit := do
  emitFileHeader
  IO.eprintln "starting emitFnDcls"
  emitFnDecls
  IO.eprintln "starting emitFns"
  let builder ← LLVM.createBuilderInContext (← getLLVMContext)
  emitFns (← getLLVMContext) (← getLLVMModule) builder
  emitInitFn (← getLLVMContext) (← getLLVMModule) builder
  emitMainFnIfNeeded (← getLLVMContext) (← getLLVMModule) builder
  emitFileFooter
  IO.eprintln (← LLVM.printModuletoString (← getLLVMModule))
  LLVM.printModuletoFile (← getLLVMModule) "/home/bollu/temp/lean-llvm.ll"
  return ()
end EmitLLVM

-- | TODO: Use a beter type signature than this.
-- | TODO: produce bitcode instead of an LLVM string.

@[export lean_ir_emit_llvm]
def emitLLVM (env : Environment) (modName : Name) (filepath: String): IO Unit := do
  let llvmctx ← LLVM.createContext
  let module ← LLVM.createModule llvmctx modName.toString -- TODO: pass module name
  let ctx := {env := env, modName := modName, llvmctx := llvmctx, llvmmodule := module}
  let initState := { var2val := default : EmitLLVM.State}
  let out? ← (EmitLLVM.main initState ctx).run
  match out? with
  | .ok _ =>  LLVM.writeBitcodeToFile ctx.llvmmodule filepath
  | .error err => IO.eprintln ("ERROR: " ++ toString err); return () -- throw (IO.userError <| toString err)
end Lean.IR
