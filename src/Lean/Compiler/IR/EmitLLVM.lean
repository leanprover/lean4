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
-- TODO: instantiate target triple and find out what size_t is.
def size_tType (ctx: @&LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  LLVM.i64Type ctx
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
  var2val: HashMap VarId (LLVM.Ptr LLVM.Value)
  jp2bb: HashMap JoinPointId (LLVM.Ptr LLVM.BasicBlock)
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
   | .compileError s => s!"compile error '{s}'"


abbrev M := StateT State (ReaderT Context (ExceptT Error IO))

instance : Inhabited (M α) where
  default := throw (Error.compileError "inhabitant")


def addVartoState (x: VarId) (v: LLVM.Ptr LLVM.Value): M Unit :=
  modify (fun s => { s with var2val := s.var2val.insert x v}) -- add new variable

def addJpTostate (jp: JoinPointId) (bb: LLVM.Ptr LLVM.BasicBlock): M Unit :=
  modify (fun s => { s with jp2bb := s.jp2bb.insert jp bb })

def emitJp (jp: JoinPointId): M (LLVM.Ptr LLVM.BasicBlock) := do
  let state ← get
  match state.jp2bb.find? jp with
  | .some bb => return bb
  | .none => throw (Error.compileError s!"unable to find join point {jp}")

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


def debugPrint (s: String): M Unit :=
  IO.eprintln $ "[debug:" ++ s ++ "]"

def constIntUnsigned (n: Nat): M (LLVM.Ptr LLVM.Value) :=  do
    LLVM.constIntUnsigned (← getLLVMContext) (UInt64.ofNat n)

-- vv emitMainFnIfIneeded vv
def getOrCreateFunctionPrototype (_ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module)
  (retty: LLVM.Ptr LLVM.LLVMType) (name: String) (args: Array (LLVM.Ptr LLVM.LLVMType)): M (LLVM.Ptr LLVM.Value) := do
  -- void lean_initialize();
  LLVM.getOrAddFunction mod name $
     (← LLVM.functionType retty args (isVarArg := false))

-- ***lean_box***
def getOrCreateLeanBoxFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidPtrType ctx) "lean_box"  #[(← LLVM.size_tType ctx)]

def callLeanBox (builder: LLVM.Ptr LLVM.Builder) (arg: LLVM.Ptr LLVM.Value) (name: String := ""): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanBoxFn) #[arg] name

-- ***void lean_mark_persistent (void *) ***--
def getOrCreateLeanMarkPersistentFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidType ctx) "lean_mark_persistent"  #[(← LLVM.voidPtrType ctx)]

def callLeanMarkPersistentFn (builder: LLVM.Ptr LLVM.Builder) (arg: LLVM.Ptr LLVM.Value): M Unit := do
  let _ ← LLVM.buildCall builder (← getOrCreateLeanMarkPersistentFn (← getLLVMContext) (← getLLVMModule)) #[arg] ""


namespace CProto
-- open Lean Elab Syntax Macro
-- Machinery to generate calling conventions for functions from their C prototypes

declare_syntax_cat ctypeish
/-
syntax "i64" : ctypeish
syntax "i32" : ctypeish
syntax "i1" : ctypeish
syntax "i8*" : ctypeish
syntax "unsigned" : ctypeish
syntax "float" : ctypeish
syntax "void" : ctypeish
syntax "double" : ctypeish

syntax "[ctypeish|" ctypeish "]" : term

macro_rules
| `([ctypeish| i64 ]) => `(LLVM.i64Type (← getLLVMContext))
| `([ctypeish| i32 ]) => `(LLVM.i32Type (← getLLVMContext))
| `([ctypeish| i1 ]) => `(LLVM.i1Type (← getLLVMContext))
| `([ctypeish| i8* ]) => `(LLVM.voidPtrType (← getLLVMContext))


open Lean Elab Term Macro in
macro (name := declareLLVMFFI) "#declareLLVMFFI" retty:ctypeish leanName:ident "->" cName: ident "(" args:ctypeish* ")" : command => do
  let nameStr : String := "getOrCreate" ++ leanName.getId.toString ++ "Fn"
  let name := mkIdentFrom leanName nameStr
  dbg_trace name
  `(def $(name) ( $args )f := 42)

#declareLLVMFFI i8* MkLeanPersistent ->  mk_lean_persistent ()
-/


end CProto

-- ***lean_{inc, dec}_{ref?}_{1,n}***
inductive RefcountKind where
| inc | dec

instance : ToString RefcountKind where
  toString
  | .inc => "inc"
  | .dec => "dec"

inductive RefcountDelta where
| one | n

deriving instance BEq for RefcountDelta

instance : ToString RefcountDelta where
  toString
  | .one => "1"
  | .n => "n"

def getOrCreateLeanRefcountFn (kind: RefcountKind) (checkRef?: Bool) (size: RefcountDelta): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidType ctx) s!"lean_{kind}{if checkRef? then "" else "_ref"}{if size == .one then "" else "_n"}"
      (if size == .one then #[← LLVM.voidPtrType ctx] else #[← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx])

def callLeanRefcountFn (builder: LLVM.Ptr LLVM.Builder)
  (kind: RefcountKind) (ref?: Bool) (arg: LLVM.Ptr LLVM.Value)
  (delta: Option (LLVM.Ptr LLVM.Value) := Option.none): M Unit := do
  match delta with
  | .none => let _ ← LLVM.buildCall builder (← getOrCreateLeanRefcountFn kind ref? RefcountDelta.one) #[arg] ""
  | .some n => let _ ← LLVM.buildCall builder (← getOrCreateLeanRefcountFn kind ref? RefcountDelta.n) #[arg, n] ""



-- **decRef1***
def getOrCreateLeanDecRefFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidType ctx) "lean_dec_ref"  #[(← LLVM.i8PtrType ctx)]

-- Do NOT attempt to merge this code with callLeanRefcountFn, because of the uber confusing
-- semantics of 'ref?'. If 'ref?' is true, it calls the version that is lean_dec
def callLeanDecRef (builder: LLVM.Ptr LLVM.Builder) (res: LLVM.Ptr LLVM.Value): M Unit := do
   let _ ← LLVM.buildCall builder (← getOrCreateLeanDecRefFn) #[res] ""



def callLeanUnsignedToNatFn (builder: LLVM.Ptr LLVM.Builder) (n: Nat) (name: String): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let mod ← getLLVMModule
  let f ←   getOrCreateFunctionPrototype ctx mod (← LLVM.voidPtrType ctx) "lean_unsigned_to_nat"  #[← LLVM.i32Type ctx]
  let nv ← LLVM.constInt32 ctx (UInt64.ofNat n)
  LLVM.buildCall builder f #[nv] name


-- **lean_mk_string_from_bytes***
def getOrCreateMkStringFromBytesFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidPtrType ctx) "lean_mk_string_from_bytes"
    #[← LLVM.voidPtrType ctx, ← LLVM.i64Type ctx]

def callLeanMkStringFromBytesFn
   (builder: LLVM.Ptr LLVM.Builder) (strPtr nBytes: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  LLVM.buildCall builder (← getOrCreateMkStringFromBytesFn ctx (← getLLVMModule)) #[strPtr, nBytes] name

-- **lean_mk_string**
def callLeanMkString
   (builder: LLVM.Ptr LLVM.Builder) (strPtr: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let fn ←  getOrCreateFunctionPrototype (← getLLVMContext)
                                         (← getLLVMModule)
                                         (← LLVM.voidPtrType ctx)
                                         "lean_mk_string"
                                          #[← LLVM.voidPtrType ctx]
  LLVM.buildCall builder fn #[strPtr] name




-- ***lean_cstr_to_nat***
-- TODO: build strings.
def getOrCreateLeanCStrToNatFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidPtrType ctx) "lean_cstr_to_nat"  #[← LLVM.voidPtrType ctx]

def callLeanCStrToNatFn (builder: LLVM.Ptr LLVM.Builder) (n: Nat) (name: String): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let f ← getOrCreateLeanCStrToNatFn ctx (← getLLVMModule)
  let s ← LLVM.buildGlobalString builder (value := toString n)
  let s ← LLVM.buildPointerCast builder s (← LLVM.i8PtrType ctx)
  LLVM.buildCall builder f #[s] name



-- ***lean_io_mk_world***
def getOrCreateLeanIOMkWorldFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- lean_object* lean_io_mk_world();
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidPtrType ctx) "lean_io_mk_world"  #[]

def callLeanIOMkWorld (builder: LLVM.Ptr LLVM.Builder): M (LLVM.Ptr LLVM.Value) := do
   LLVM.buildCall builder (← getOrCreateLeanIOMkWorldFn (← getLLVMContext) (← getLLVMModule)) #[] "mk_io_out"


-- ***bool lean_io_result_is_err(lean_object *o);***
def getOrCreateLeanIOResultIsErrorFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  getOrCreateFunctionPrototype ctx mod (← LLVM.i1Type ctx) "lean_io_result_is_error"  #[(← LLVM.voidPtrType ctx)]

def callLeanIOResultIsError (builder: LLVM.Ptr LLVM.Builder) (arg: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanIOResultIsErrorFn (← getLLVMContext) (← getLLVMModule)) #[arg] name

/-
-- ***lean_object *lean_io_result_get_value(lean_object *o)***
def getOrCreateLeanIOResultGetValueFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidPtrType ctx) "lean_io_result_get_value"  #[(← LLVM.voidPtrType ctx)]

def callLeanIOResultGetValueFn (builder: LLVM.Ptr LLVM.Builder) (arg: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanIOResultGetValueFn (← getLLVMContext) (← getLLVMModule)) #[arg] name
-/



-- lean_alloc_ctor (unsigned tag, unsigned num_obj, unsigned scalar_sz)
def getOrCreateLeanAllocCtorFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  -- let unsigned ← LLVM.size_tType ctx
  let i32 ← LLVM.i32Type ctx
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidPtrType ctx) "lean_alloc_ctor"  #[i32, i32, i32]

def callLeanAllocCtor (builder: LLVM.Ptr LLVM.Builder) (tag num_objs scalar_sz: Nat) (name: String := ""): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let tag ← LLVM.constInt32 ctx (UInt64.ofNat tag)
  let num_objs ← LLVM.constInt32 ctx (UInt64.ofNat num_objs)
  let scalar_sz ← LLVM.constInt32 ctx (UInt64.ofNat scalar_sz)
  LLVM.buildCall builder (← getOrCreateLeanAllocCtorFn) #[tag, num_objs, scalar_sz] name

-- void lean_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v)
def getOrCreateLeanCtorSetFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let unsigned ← LLVM.size_tType ctx
  let voidptr ← LLVM.voidPtrType ctx
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidType ctx) "lean_ctor_set"  #[voidptr, unsigned, voidptr]

-- TODO(bollu): remove name from this, since it returns void.
def callLeanCtorSet (builder: LLVM.Ptr LLVM.Builder) (o i v: LLVM.Ptr LLVM.Value) (name: String := ""): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanCtorSetFn) #[o, i, v] name


-- lean_obj_res io_result_mk_ok(lean_obj_arg a)
def getOrCreateLeanIOResultMkOkFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let voidptr ← LLVM.voidPtrType ctx
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    voidptr "lean_io_result_mk_ok"  #[voidptr]

def callLeanIOResultMKOk (builder: LLVM.Ptr LLVM.Builder) (v: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanIOResultMkOkFn) #[v] name



-- ***void* lean_obj_res lean_alloc_closure(void * fun, unsigned arity, unsigned num_fixed)***
def callLeanAllocClosureFn (builder: LLVM.Ptr LLVM.Builder) (f arity nys: LLVM.Ptr LLVM.Value) (retName: String): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_alloc_closure"
  let retty ← LLVM.voidPtrType ctx
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx, ← LLVM.size_tType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  LLVM.buildCall builder fn  #[f, arity, nys] retName

-- ***void lean_closure_set(u_lean_obj_arg o, unsigned i, lean_obj_arg a)***
def callLeanClosureSetFn (builder: LLVM.Ptr LLVM.Builder) (closure ix arg: LLVM.Ptr LLVM.Value) (retName: String): M Unit := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_closure_set"
  let retty ← LLVM.voidType ctx
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx, ← LLVM.voidPtrType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let _ ← LLVM.buildCall builder fn  #[closure, ix, arg] retName


-- ***int lean_obj_tag(lean_obj_arg o)***
def callLeanObjTag (builder: LLVM.Ptr LLVM.Builder) (closure: LLVM.Ptr LLVM.Value) (retName: String): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_obj_tag"
  let retty ← LLVM.i32Type ctx
  let argtys := #[ ← LLVM.voidPtrType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let out ← LLVM.buildCall builder fn  #[closure] retName
  LLVM.buildSextOrTrunc builder out (← LLVM.i64Type ctx)

-- ***lean_io_result_get_value**
def getOrCreateLeanIOResultGetValueFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidPtrType ctx) "lean_io_result_get_value"  #[← LLVM.voidPtrType ctx]

def callLeanIOResultGetValue (builder: LLVM.Ptr LLVM.Builder) (v: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
   LLVM.buildCall builder (← getOrCreateLeanIOResultGetValueFn) #[v] name


-- TODO(bollu): what does this actually release?
-- ** void lean_ctor_release (lean_obj_arg o, int i)***
def callLeanCtorRelease (builder: LLVM.Ptr LLVM.Builder)
  (closure i: LLVM.Ptr LLVM.Value) (retName: String := ""): M Unit := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_ctor_release"
  let retty ← LLVM.voidType ctx
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let _ ← LLVM.buildCall builder fn  #[closure, i] retName


-- ** void lean_ctor_set_tag (lean_obj_arg o, int new_tag)***
def callLeanCtorSetTag (builder: LLVM.Ptr LLVM.Builder)
  (closure i: LLVM.Ptr LLVM.Value) (retName: String := ""): M Unit := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_ctor_set_tag"
  let retty ← LLVM.voidType ctx
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let _ ← LLVM.buildCall builder fn  #[closure, i] retName




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
def toLLVMType (t: IRType): M (LLVM.Ptr LLVM.LLVMType) := do
  let ctx ← getLLVMContext
  match t with
  | IRType.float      => LLVM.doubleTypeInContext ctx
  | IRType.uint8      => LLVM.intTypeInContext ctx 8
  | IRType.uint16     => LLVM.intTypeInContext ctx 16
  | IRType.uint32     => LLVM.intTypeInContext ctx 32
  | IRType.uint64     => LLVM.intTypeInContext ctx 64
  -- TODO: how to cleanly size_t in LLVM? We can do eg. instantiate the current target and query for size.
  | IRType.usize      => LLVM.size_tType ctx
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

/-
def toCInitName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => return "_init_" ++ s
  | some _                   => throwInvalidExportName n
  | none                     => pure ("_init_" ++ n.mangle)
-/
def toCInitName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => return "_init_" ++ s
  | some _                   => throwInvalidExportName n
  | none                     => pure ("_init_" ++ n.mangle)


-- vvvv LLVM UTILS vvvv

-- indicates whether the API for building the blocks for then/else should
-- forward the control flow to the merge block.
-- TODO: infer this automatically from the state of the basic block.
inductive ShouldForwardControlFlow where
| yes | no

-- Get the function we are currently inserting into.
def builderGetInsertionFn (builder: LLVM.Ptr LLVM.Builder): M (LLVM.Ptr LLVM.Value) := do
  let builderBB ← LLVM.getInsertBlock builder
  LLVM.getBasicBlockParent builderBB

def builderAppendBasicBlock (builder: LLVM.Ptr LLVM.Builder) (name: String): M (LLVM.Ptr LLVM.BasicBlock) := do
  let fn ← builderGetInsertionFn builder
  LLVM.appendBasicBlockInContext (← getLLVMContext) fn name


def buildWhile_ (builder: LLVM.Ptr LLVM.Builder) (name: String)
  (condcodegen: LLVM.Ptr LLVM.Builder → M (LLVM.Ptr LLVM.Value))
  (bodycodegen: LLVM.Ptr LLVM.Builder → M Unit): M Unit := do
  debugPrint "buildWhile_"
  let fn ← builderGetInsertionFn builder

  let nameHeader := name ++ "header"
  let nameBody := name ++ "body"
  let nameMerge := name ++ "merge"

  -- cur → header
  let headerbb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn nameHeader
  let _ ← LLVM.buildBr builder headerbb

  let bodybb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn nameBody
  let mergebb ← LLVM.appendBasicBlockInContext (← getLLVMContext) fn nameMerge

  -- header → {body, merge}
  LLVM.positionBuilderAtEnd builder headerbb
  let cond ← condcodegen builder
  -- LLVM.positionBuilderAtEnd builder headerbb
  let _ ← LLVM.buildCondBr builder cond bodybb mergebb

  -- body → header
  LLVM.positionBuilderAtEnd builder bodybb
  bodycodegen builder
  -- LLVM.positionBuilderAtEnd builder bodybb
  let _ ← LLVM.buildBr builder headerbb

  -- merge
  LLVM.positionBuilderAtEnd builder mergebb


-- build an if, and position the builder at the merge basic block after execution.
-- The '_' denotes that we return Unit on each branch.
-- TODO: get current function from the builder.
def buildIfThen_ (builder: LLVM.Ptr LLVM.Builder) (name: String) (brval: LLVM.Ptr LLVM.Value)
  (thencodegen: LLVM.Ptr LLVM.Builder → M ShouldForwardControlFlow): M Unit := do
  let fn ← builderGetInsertionFn builder
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
  -- LLVM.positionBuilderAtEnd builder thenbb
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
  -- LLVM.positionBuilderAtEnd builder thenbb
  match fwd? with
  | .yes => let _ ← LLVM.buildBr builder mergebb
  | .no => pure ()
  -- else
  LLVM.positionBuilderAtEnd builder elsebb
  let fwd? ← elsecodegen builder
  -- LLVM.positionBuilderAtEnd builder elsebb
  match fwd? with
  | .yes => let _ ← LLVM.buildBr builder mergebb
  | .no => pure ()
  -- merge
  LLVM.positionBuilderAtEnd builder mergebb

-- recall that lean uses `i8` for booleans, not `i1`, so we need to compare with `true`.
def buildLeanBoolTrue? (builder: LLVM.Ptr LLVM.Builder) (b: LLVM.Ptr LLVM.Value) (name: String := ""): M (LLVM.Ptr LLVM.Value) := do
   let ctx ← getLLVMContext
   LLVM.buildICmp builder LLVM.IntPredicate.NE b (← LLVM.constInt8 ctx 0) name



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
  debugPrint "emitFnDeclAux"
  IO.println s!"\nvv\nemitFnDeclAux {decl}\n^^"
  -- let types : Array LLVM.LLVMType ← decl.params.mapM (toLLVMType ctx)
  let ps := decl.params
  let env ← getEnv
  -- bollu: if we have a declaration with no parameters, then we emit it as a global pointer.
  -- bollu: Otherwise, it gets emitted as a function
  -- if ps.isEmpty then
  --   if isClosedTermName env decl.name then emit "static "
  --   else if isExternal then emit "extern "
  --   else emit "LEAN_EXPORT "
  -- else
  --   if !isExternal then emit "LEAN_EXPORT "
  -- emit (toCType decl.resultType ++ " " ++ cppBaseName)
  if ps.isEmpty then
      -- bollu, TODO: handle `extern` specially?
      let retty ← (toLLVMType decl.resultType)
      let global ← LLVM.getOrAddGlobal mod cppBaseName retty
      if !isExternal then
        LLVM.setInitializer global (← LLVM.getUndef retty)
      return global
  else
      IO.eprintln s!"creating result type ({decl.resultType})"
      let retty ← (toLLVMType decl.resultType)
      IO.eprintln s!"...created!"
      let mut argtys := #[]
      for p in ps do
        -- if it is extern, then we must not add irrelevant args
        if !(isExternC env decl.name) || !p.ty.isIrrelevant then
          IO.eprintln s!"adding argument of type {p.ty}"
          argtys := argtys.push (← toLLVMType p.ty)
          IO.eprintln "...added argument!"
      -- QUESTION: why do we care if it is boxed?
      -- TODO (bollu): simplify this API, this code of `closureMaxArgs` is duplicated in multiple places.
      if argtys.size > closureMaxArgs && isBoxedName decl.name then
        argtys := #[← LLVM.pointerType (← LLVM.voidPtrType ctx)]
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



-- vvv emitVDecl.emitCtor
-- TODO: think if I need to actually load the value from the slot here.
def emitLhsSlot_ (x: VarId): M (LLVM.Ptr LLVM.Value) := do
  let state ← get
  match state.var2val.find? x with
  | .some v => return v
  | .none => throw (Error.compileError s!"unable to find variable {x}")

def emitLhsVal (builder: LLVM.Ptr LLVM.Builder) (x: VarId) (name: String := ""): M (LLVM.Ptr LLVM.Value) := do
  let xslot ← emitLhsSlot_ x
  LLVM.buildLoad builder xslot name

def emitLhsSlotStore (builder: LLVM.Ptr LLVM.Builder) (x: VarId) (v: LLVM.Ptr LLVM.Value): M Unit := do
  let slot ← emitLhsSlot_ x
  LLVM.buildStore builder v slot




/-
def argToCString (x : Arg) : String :=
  match x with
  | Arg.var x => toString x
  | _         => "lean_box(0)"

def emitArg (x : Arg) : M Unit :=
  emit (argToCString x)
-/
def emitArgSlot_ (builder: LLVM.Ptr LLVM.Builder) (x : Arg) : M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  match x with
  | Arg.var x => emitLhsSlot_ x
  | _ => do
    let slot ← LLVM.buildAlloca builder (← LLVM.voidPtrType ctx) "irrelevant_slot"
    let v ← callLeanBox builder (← LLVM.constIntUnsigned ctx 0) "irrelevant_val"
    let _ ← LLVM.buildStore builder v slot
    return slot

def emitArgVal (builder: LLVM.Ptr LLVM.Builder) (x: Arg) (name: String := ""): M (LLVM.Ptr LLVM.Value) := do
  debugPrint "emitArgVal"
  let xslot ← emitArgSlot_ builder x
  LLVM.buildLoad builder xslot name
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
  debugPrint s!"emitAllocCtor {c.name}     cidx {c.cidx}     size {c.size}"
  -- throw (Error.unimplemented "emitAllocCtor")
  -- TODO(bollu): find the correct size.
  -- TODO(bollu): don't assume void * size is 8
  let hackSizeofVoidPtr := 8
  let scalarSize := hackSizeofVoidPtr * c.usize + c.ssize; -- HACK: do find the correct size.
  -- let idx ← LLVM.constIntUnsigned ctx (UInt64.ofNat c.cidx)
  -- let size ← LLVM.constIntUnsigned ctx (UInt64.ofNat c.size)
  -- let scalarSize ← LLVM.constIntUnsigned ctx (UInt64.ofNat scalarSize)
  callLeanAllocCtor builder c.cidx c.size scalarSize "lean_alloc_ctor_out"
/-
def emitCtorSetArgs (z : VarId) (ys : Array Arg) : M Unit :=
  ys.size.forM fun i => do
    emit "lean_ctor_set("; emit z; emit ", "; emit i; emit ", "; emitArgSlot_ ys[i]!; emitLn ");"
-/
def emitCtorSetArgs (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (ys : Array Arg) : M Unit := do
  ys.size.forM fun i => do
    let zv ← emitLhsVal builder z
    let yv ← emitArgVal builder ys[i]!
    let iv ← LLVM.constIntUnsigned (← getLLVMContext) (UInt64.ofNat i)
    let _ ← callLeanCtorSet builder zv iv yv ""
    emitLhsSlotStore builder z zv
    pure ()
/-
def emitCtor (z : VarId) (c : CtorInfo) (ys : Array Arg) : M Unit := do
  emitLhsSlot_ z;
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    emit "lean_box("; emit c.cidx; emitLn ");"
  else do
    emitAllocCtor c; emitCtorSetArgs z ys
-/
def emitCtor (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (c : CtorInfo) (ys : Array Arg) : M Unit := do
  debugPrint "emitCtor"
  let slot ← emitLhsSlot_ z;
  addVartoState z slot
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    let v ← callLeanBox builder (← constIntUnsigned c.cidx) "lean_box_outv"
    let _ ← LLVM.buildStore builder v slot
  else do
    let v ← emitAllocCtor builder c;
    let _ ← LLVM.buildStore builder v slot
    emitCtorSetArgs builder z ys -- TODO:
    IO.eprintln "######5#######"


-- ^^^ emitVDecl.emitCtor

-- vvv emitVDecl vvv
/-
def emitInc (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
  emit $
    if checkRef then (if n == 1 then "lean_inc" else "lean_inc_n")
    else (if n == 1 then "lean_inc_ref" else "lean_inc_ref_n")
  emit "("; emit x
  if n != 1 then emit ", "; emit n
  emitLn ");"
-/

def emitInc (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
  let xv ← emitLhsVal builder x
  if n != 1
  then do
     let nv ← LLVM.constIntUnsigned (← getLLVMContext) (UInt64.ofNat n)
     callLeanRefcountFn builder (kind := RefcountKind.inc) (ref? := checkRef) (delta := nv) xv
  else callLeanRefcountFn builder (kind := RefcountKind.inc) (ref? := checkRef) xv


/-
def emitDec (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
  emit (if checkRef then "lean_dec" else "lean_dec_ref");
  emit "("; emit x;
  if n != 1 then emit ", "; emit n
  emitLn ");"
-/

def emitDec (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (n : Nat) (checkRef : Bool) : M Unit := do
  let xv ← emitLhsVal builder x
  if n != 1
  then throw (Error.compileError "expected n = 1 for emitDec")
  else callLeanRefcountFn builder (kind := RefcountKind.dec) (ref? := checkRef) xv



/-
def emitNumLit (t : IRType) (v : Nat) : M Unit := do
  if t.isObj then
    if v < UInt32.size then
      emit "lean_unsigned_to_nat("; emit v; emit "u)"
    else
      emit "lean_cstr_to_nat(\""; emit v; emit "\")"
  else
    emit v
-/
def emitNumLit (builder: LLVM.Ptr LLVM.Builder) (t : IRType) (v : Nat) : M (LLVM.Ptr LLVM.Value) := do
  debugPrint "emitNumLit"
  if t.isObj then
    if v < UInt32.size then
      callLeanUnsignedToNatFn builder v ""
      -- emit "lean_unsigned_to_nat("; emit v; emit "u)"
    else
      callLeanCStrToNatFn builder v ""
      -- emit "lean_cstr_to_nat(\""; emit v; emit "\")"
  else
    -- LLVM.constIntUnsigned (← getLLVMContext) (UInt64.ofNat v)
    LLVM.constInt (← toLLVMType t) (UInt64.ofNat v)

def toHexDigit (c : Nat) : String :=
  String.singleton c.digitChar

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
      -- TODO(Leo): we should use `\unnnn` for escaping unicode characters.
      else String.singleton c)
    q;
  q ++ "\""


/-
def toStringArgs (ys : Array Arg) : List String :=
  ys.toList.map argToCString
-/

/-
def emitSimpleExternalCall (f : String) (ps : Array Param) (ys : Array Arg) : M Unit := do
  emit f; emit "("
  -- We must remove irrelevant arguments to extern calls.
  discard <| ys.size.foldM
    (fun i (first : Bool) =>
      if ps[i]!.ty.isIrrelevant then
        pure first
      else do
        unless first do emit ", "
        emitArgSlot_ ys[i]!
        pure false)
    true
  emitLn ");"
  pure ()
-/

def emitSimpleExternalCall
  (builder: LLVM.Ptr LLVM.Builder) (f : String) (ps : Array Param) (ys : Array Arg)
  (retty: IRType) (name: String): M (LLVM.Ptr LLVM.Value) := do
  let mut args := #[]
  let mut argTys := #[]
  for (p, y) in ps.zip ys do
    if !p.ty.isIrrelevant then
      argTys := argTys.push (← toLLVMType p.ty)
      args := args.push (← emitArgVal builder y "")
  let fnty ← LLVM.functionType (← toLLVMType retty) argTys
  let fn ← LLVM.getOrAddFunction (← getLLVMModule) f fnty
  LLVM.buildCall builder fn args name




def emitExternCall (builder: LLVM.Ptr LLVM.Builder)
  (f : FunId)
  (ps : Array Param)
  (extData : ExternAttrData)
  (ys : Array Arg) (retty: IRType)
  (name: String): M (LLVM.Ptr LLVM.Value) :=
  match getExternEntryFor extData `c with
  | some (ExternEntry.standard _ extFn) => emitSimpleExternalCall builder extFn ps ys retty name
  | some (ExternEntry.inline "llvm" _pat)     => throw (Error.unimplemented "unimplemented codegen of inline LLVM")
  | some (ExternEntry.inline _ _pat)     => throw (Error.compileError "cannot codegen non-LLVM inline code")
  | some (ExternEntry.foreign _ extFn)  => emitSimpleExternalCall builder extFn ps ys retty name
  | _ => throw (Error.compileError s!"failed to emit extern application '{f}'")

/--
Create a function declaration and return a pointer to the function.
If the function actually takes arguments, then we must have a function pointer in scope.
If the function takes no arguments, then it is a top-level closed term, and its value will
be stored in a global pointer. So, we load from the global pointer. The type of the global is function pointer pointer.
This returns a *function pointer.*
-/
def getOrAddFunIdValue (builder: LLVM.Ptr LLVM.Builder) (f: FunId): M (LLVM.Ptr LLVM.Value) := do
  debugPrint s!"getOrAddFnIdValue {f}"
  let decl ← getDecl f
  let fcname ← toCName f
  let retty ← toLLVMType decl.resultType
  if decl.params.isEmpty then
     let gslot ← LLVM.getOrAddGlobal (← getLLVMModule) fcname retty
     LLVM.buildLoad builder gslot ""
  else
    let argtys ← decl.params.mapM (fun p => do toLLVMType p.ty)
    let fnty ← LLVM.functionType retty argtys
    LLVM.getOrAddFunction (← getLLVMModule) fcname fnty


/-
def emitPartialApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
  let decl ← getDecl f
  let arity := decl.params.size;
  emitLhsSlot_ z; emit "lean_alloc_closure((void*)("; emitCName f; emit "), "; emit arity; emit ", "; emit ys.size; emitLn ");";
  ys.size.forM fun i => do
    let y := ys[i]!
    emit "lean_closure_set("; emit z; emit ", "; emit i; emit ", "; emitArgSlot_ y; emitLn ");"
-/

def emitPartialApp (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
  debugPrint "emitPartialApp"
  let decl ← getDecl f
  let fv ← getOrAddFunIdValue builder f
  let arity := decl.params.size;
  let zslot ← emitLhsSlot_ z
  let fv_voidptr ← LLVM.buildPointerCast builder fv (← LLVM.voidPtrType (← getLLVMContext)) ""
  let zval ← callLeanAllocClosureFn builder fv_voidptr
                                    (← constIntUnsigned arity)
                                    (← constIntUnsigned ys.size) ""
  LLVM.buildStore builder zval zslot
  ys.size.forM fun i => do
    let yslot ← emitArgSlot_ builder ys[i]!
    let yval ← LLVM.buildLoad builder yslot ""
    callLeanClosureSetFn builder zval (← constIntUnsigned i) yval ""

/-
def emitApp (z : VarId) (f : VarId) (ys : Array Arg) : M Unit :=
  if ys.size > closureMaxArgs then do
    emit "{ lean_object* _aargs[] = {"; emitArgs ys; emitLn "};";
    emitLhs z; emit "lean_apply_m("; emit f; emit ", "; emit ys.size; emitLn ", _aargs); }"
  else do
    emitLhs z; emit "lean_apply_"; emit ys.size; emit "("; emit f; emit ", "; emitArgs ys; emitLn ");"
-/
def emitApp (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (f : VarId) (ys : Array Arg) : M Unit := do
  let ctx ← getLLVMContext
  if ys.size > closureMaxArgs then do
    let aargs ← LLVM.buildAlloca builder (← LLVM.arrayType (← LLVM.voidPtrType ctx) (UInt64.ofNat ys.size)) "aargs"
    for i in List.range ys.size do
      let yv ← emitArgVal builder ys[i]!
      let aslot ← LLVM.buildInBoundsGEP builder aargs #[← constIntUnsigned 0, ← constIntUnsigned i] s!"param_{i}_slot"
      LLVM.buildStore builder yv aslot
    -- lean_apply_m --
    let fnName :=  s!"lean_apply_m"
    let retty ← LLVM.voidPtrType (← getLLVMContext)
    let args := #[← emitLhsVal builder f, ← constIntUnsigned ys.size, aargs]
    -- '1 + ...', '1' for the fn and 'args' for the arguments
    let argtys := #[← LLVM.voidPtrType (← getLLVMContext)]
    let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
    let zv ← LLVM.buildCall builder fn args
    emitLhsSlotStore builder z zv
  else do
    let ctx ← getLLVMContext
    let fnName :=  s!"lean_apply_{ys.size}"
    let retty ← LLVM.voidPtrType (← getLLVMContext)
    let args := #[← emitLhsVal builder f] ++ (← ys.mapM (emitArgVal builder))
    -- '1 + ...', '1' for the fn and 'args' for the arguments
    let argtys := (List.replicate (1 + ys.size) (← LLVM.voidPtrType ctx)).toArray
    let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
    let zv ← LLVM.buildCall builder fn args
    emitLhsSlotStore builder z zv


/-

def emitFullApp (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
  emitLhsSlot_ z
  let decl ← getDecl f
  match decl with
  | Decl.extern _ ps _ extData => emitExternCall f ps extData ys
  | _ =>
    emitCName f
    if ys.size > 0 then emit "("; emitArgSlot_s ys; emit ")"
    emitLn ";"
-/
def emitFullApp (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (f : FunId) (ys : Array Arg) : M Unit := do
  debugPrint s!"emitFullApp z:{z} f:{f} ys:?"
  let zslot ← emitLhsSlot_ z
  let decl ← getDecl f
  match decl with
  | Decl.extern _ ps retty extData =>
     -- throw (Error.compileError "emitFullApp.Decl.extern")
     let zv ← emitExternCall builder f ps extData ys retty ""
     LLVM.buildStore builder zv zslot
  | _ =>
    /-
    let fcname ← toCName f
    let fv ← match  (← LLVM.getNamedFunction (← getLLVMModule) fcname) with
           | .some fv => pure fv
           | .none => throw (α := LLVM.Ptr LLVM.Value) (Error.compileError s!"unable to find function {f}")
    -/
    if ys.size > 0 then
        let fv ← getOrAddFunIdValue builder f
        let ys ←  ys.mapM (fun y => do
            let yslot ← emitArgSlot_ builder y
            let yv ← LLVM.buildLoad builder yslot ""
            return yv)
        let zv ← LLVM.buildCall builder fv ys ""
        LLVM.buildStore builder zv zslot
    else
       let zv ← getOrAddFunIdValue builder f
       LLVM.buildStore builder zv zslot

   -- if ys.size > 0 then emit "("; emitArgSlot_s ys; emit ")"
  -- emitLn ";"


/-
def emitLit (z : VarId) (t : IRType) (v : LitVal) : M Unit := do
  emitLhsSlot_ z;
  match v with
  | LitVal.num v => emitNumLit t v; emitLn ";"
  | LitVal.str v => emit "lean_mk_string_from_bytes("; emit (quoteString v); emit ", "; emit v.utf8ByteSize; emitLn ");"
-/
-- Note that this returns a *slot*, just like `emitLhsSlot_`.
def emitLit (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (t : IRType) (v : LitVal) : M (LLVM.Ptr LLVM.Value) := do
  debugPrint "emitLit"
  let zslot ← LLVM.buildAlloca builder (← toLLVMType t) ""
  addVartoState z zslot
  let zv ← match v with
            | LitVal.num v => emitNumLit builder t v -- emitNumLit t v; emitLn ";"
            | LitVal.str v =>
                 -- TODO (bollu): We should be able to get the underlying UTF8 data and send it to LLVM.
                 -- TODO (bollu): do we need to quote the string for LLVM?
                 -- let str_global ← LLVM.buildGlobalString builder (quoteString v) "" -- (v.utf8ByteSiz)
                 let str_global ← LLVM.buildGlobalString builder v "" -- (v.utf8ByteSiz)
                 -- access through the global, into the 0th index of the array
                 let zero ← LLVM.constIntUnsigned (← getLLVMContext) 0
                 let strPtr ← LLVM.buildInBoundsGEP builder str_global  #[zero, zero] ""
                 let nbytes ← LLVM.constIntUnsigned (← getLLVMContext) (UInt64.ofNat (v.utf8ByteSize))
                 callLeanMkStringFromBytesFn builder strPtr nbytes ""
  LLVM.buildStore builder zv zslot
  return zslot



-- ***void *lean_ctor_get(void *obj, int ix)***
def callLeanCtorGet (builder: LLVM.Ptr LLVM.Builder) (x i: LLVM.Ptr LLVM.Value) (retName: String): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_ctor_get"
  let retty ← LLVM.voidPtrType (← getLLVMContext)
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.i32Type ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let i ← LLVM.buildSextOrTrunc builder i (← LLVM.i32Type ctx)
  LLVM.buildCall builder fn  #[x, i] retName


def emitProj (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (i : Nat) (x : VarId) : M Unit := do
  debugPrint "emitProj"
  let xval ← emitLhsVal builder x
  let zval ← callLeanCtorGet builder xval (← constIntUnsigned i) ""
  emitLhsSlotStore builder z zval

-- ***usize lean_ctor_get_usize(void *obj, int ix)***
def callLeanCtorGetUsize (builder: LLVM.Ptr LLVM.Builder) (x i: LLVM.Ptr LLVM.Value) (retName: String): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_ctor_get_usize"
  let retty ← LLVM.size_tType ctx
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  LLVM.buildCall builder fn  #[x, i] retName


def emitUProj (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (i : Nat) (x : VarId) : M Unit := do
  debugPrint "emitUProj"
  let xval ← emitLhsVal builder x
  let zval ← callLeanCtorGetUsize builder xval (← constIntUnsigned i) ""
  emitLhsSlotStore builder z zval

/-
def emitOffset (n : Nat) (offset : Nat) : M Unit := do
  if n > 0 then
    emit "sizeof(void*)*"; emit n;
    if offset > 0 then emit " + "; emit offset
  else
    emit offset
-/
-- TODO, bollu: check this code very very properly.
-- TODO, bollu: this is a GEP calculation?
-- TODO, bollu: surely it is possible to do this better?
def emitOffset (builder: LLVM.Ptr LLVM.Builder )(n : Nat) (offset : Nat) : M (LLVM.Ptr LLVM.Value) := do
  debugPrint "emitOffset"
   let ctx ← getLLVMContext
   let basety ← LLVM.pointerType (← LLVM.i8Type ctx)
   let _basev ← LLVM.constPointerNull basety
   -- https://stackoverflow.com/questions/14608250/how-can-i-find-the-size-of-a-type
   -- let gepVoidPtrAt1 ← LLVM.buildGEP builder basev #[(← constIntUnsigned 1)] "gep_void_1"
   -- let out ← LLVM.buildPtrToInt builder gepVoidPtrAt1 (← LLVM.size_tType ctx)  "gep_size_void*" -- sizeof(void*)
   -- TODO(bollu): replace 8 with sizeof(void*)
   let out ← constIntUnsigned 8
   let out ← LLVM.buildMul builder out (← constIntUnsigned n) "" -- sizeof(void*)*n
   LLVM.buildAdd builder out (← constIntUnsigned offset) "" -- sizeof(void*)*n+offset


def emitSProj (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (t : IRType) (n offset : Nat) (x : VarId) : M Unit := do
  debugPrint "emitSProj"
  let ctx ← getLLVMContext
  let (fnName, retty) ←
    match t with
    | IRType.float  => pure ("lean_ctor_get_float", ← LLVM.doubleTypeInContext ctx)
    | IRType.uint8  => pure ("lean_ctor_get_uint8", ← LLVM.i8Type ctx)
    | IRType.uint16 => pure ("lean_ctor_get_uint16", ←  LLVM.i16Type ctx)
    | IRType.uint32 => pure ("lean_ctor_get_uint32", ← LLVM.i32Type ctx)
    | IRType.uint64 => pure ("lean_ctor_get_uint64", ← LLVM.i64Type ctx)
    | _             => throw (Error.compileError "invalid instruction")
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let xval ← emitLhsVal builder x
  let offset ← emitOffset builder n offset
  let zval ← LLVM.buildCall builder fn  #[xval, offset] ""
  emitLhsSlotStore builder z zval


-- ***bool lean_is_exclusive(lean_obj_arg o)***
def callLeanIsExclusive (builder: LLVM.Ptr LLVM.Builder) (closure: LLVM.Ptr LLVM.Value) (retName: String := ""): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_is_exclusive"
  let retty ← LLVM.i1Type ctx -- TODO (bollu): Lean uses i8 instead of i1 for booleans because C things?
  let argtys := #[ ← LLVM.voidPtrType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let out ← LLVM.buildCall builder fn  #[closure] retName
  LLVM.buildSextOrTrunc builder out (← LLVM.i8Type ctx)

-- ***bool lean_is_scalar(lean_obj_arg o)***
def callLeanIsScalar (builder: LLVM.Ptr LLVM.Builder) (closure: LLVM.Ptr LLVM.Value) (retName: String := ""): M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_is_scalar"
  let retty ← LLVM.i8Type ctx -- TODO (bollu): Lean uses i8 instead of i1 for booleans because C things?
  let argtys := #[ ← LLVM.voidPtrType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  LLVM.buildCall builder fn  #[closure] retName

 -- emitLhs z; emit "!lean_is_exclusive("; emit x; emitLn ");"

def emitIsShared (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (x : VarId) : M Unit := do
    debugPrint "emitIsShared"
    let xv ← emitLhsVal builder x
    let exclusive? ← callLeanIsExclusive builder xv
    let exclusive? ← LLVM.buildSextOrTrunc builder exclusive? (← LLVM.i1Type (← getLLVMContext))
    -- let exclusive? ← buildLeanBoolTrue? builder exclusive?
    let shared? ← LLVM.buildNot builder exclusive?
    let shared? ← LLVM.buildSext builder shared? (← LLVM.i8Type (← getLLVMContext))
    emitLhsSlotStore builder z shared?


def emitBox (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (x : VarId) (xType: IRType): M Unit := do
  let ctx ← getLLVMContext
  let xv ← emitLhsVal builder x
  let (fnName, argTy, xv) ←
    match xType with
    | IRType.usize  => pure ("lean_box_usize", ← LLVM.size_tType ctx, xv)
    | IRType.uint32 => pure ("lean_box_uint32", ← LLVM.i32Type ctx, xv)
    | IRType.uint64 => pure ("lean_box_uint64", ← LLVM.size_tType ctx, xv)
    | IRType.float  => pure ("lean_box_float", ← LLVM.doubleTypeInContext ctx, xv)
    | _             => do
         -- sign extend smaller values into i64
         let xv ← LLVM.buildSext builder xv (← LLVM.size_tType ctx)
         pure ("lean_box", ← LLVM.size_tType ctx, xv)
  let ctx ← getLLVMContext
  let retty ← LLVM.voidPtrType ctx -- TODO (bollu): Lean uses i8 instead of i1 for booleans because C things?
  let argtys := #[argTy]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let zv ← LLVM.buildCall builder fn  #[xv] ""
  emitLhsSlotStore builder z zv


def emitUnbox (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (t : IRType) (x : VarId) (retName: String := ""): M Unit := do
  let ctx ← getLLVMContext
  let (fnName, retty) ←
     match t with
     | IRType.usize  => pure ("lean_unbox_usize", ← toLLVMType t)
     | IRType.uint32 => pure ("lean_unbox_uint32", ← toLLVMType t)
     | IRType.uint64 => pure ("lean_unbox_uint64", ← toLLVMType t)
     | IRType.float  => pure ("lean_unbox_float", ← toLLVMType t)
     | _             => pure ("lean_unbox", ← LLVM.size_tType ctx)
  let argtys := #[← LLVM.voidPtrType ctx ]
  -- let retty ← toLLVMType t
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let zval ← LLVM.buildCall builder fn #[← emitLhsVal builder x] retName
  -- TODO(bollu): note that lean_unbox only returns an i64, but we may need to truncate to
  -- smaller widths. see `phashmap` for an example of this occurring at calls to `lean_unbox`
  let zval ← LLVM.buildSextOrTrunc builder zval (← toLLVMType t)
  emitLhsSlotStore builder z zval


/-
def emitReset (z : VarId) (n : Nat) (x : VarId) : M Unit := do
  emit "if (lean_is_exclusive("; emit x; emitLn ")) {";
  n.forM fun i => do
    emit " lean_ctor_release("; emit x; emit ", "; emit i; emitLn ");"
  emit " "; emitLhs z; emit x; emitLn ";";


  emitLn "} else {";
  emit " lean_dec_ref("; emit x; emitLn ");";
  emit " "; emitLhs z; emitLn "lean_box(0);";
  emitLn "}"
-/
def emitReset (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (n : Nat) (x : VarId) : M Unit := do
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
/-
def emitReuse (z : VarId) (x : VarId) (c : CtorInfo) (updtHeader : Bool) (ys : Array Arg) : M Unit := do
  emit "if (lean_is_scalar("; emit x; emitLn ")) {";
  emit " "; emitLhs z; emitAllocCtor c;
  emitLn "} else {";
  emit " "; emitLhs z; emit x; emitLn ";";
  if updtHeader then emit " lean_ctor_set_tag("; emit z; emit ", "; emit c.cidx; emitLn ");"
  emitLn "}";
  emitCtorSetArgs z ys
-/
def emitReuse (builder: LLVM.Ptr LLVM.Builder)
  (z : VarId) (x : VarId) (c : CtorInfo) (updtHeader : Bool) (ys : Array Arg) : M Unit := do
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
def emitVDecl (builder: LLVM.Ptr LLVM.Builder) (z : VarId) (t : IRType) (v : Expr) : M Unit := do
  debugPrint "emitVDecl"
  match v with
  | Expr.ctor c ys      => emitCtor builder z c ys -- throw (Error.unimplemented "emitCtor z c ys")
  | Expr.reset n x      =>
     if ResetReuse.shouldEmitResetReuse? then emitReset builder z n x else throw (Error.unimplemented "emitReset")
  | Expr.reuse x c u ys =>
     if ResetReuse.shouldEmitResetReuse? then emitReuse builder z x c u ys else throw (Error.unimplemented "emitReuse")
  | Expr.proj i x       => emitProj builder z i x
  | Expr.uproj _i _x      => throw (Error.unimplemented "emitUProj z i x")
  | Expr.sproj n o x    => emitSProj builder z t n o x
  | Expr.fap c ys       => emitFullApp builder z c ys
  | Expr.pap c ys       => emitPartialApp builder z c ys
  | Expr.ap x ys        => emitApp builder z x ys -- throw (Error.unimplemented "emitApp z x ys")
  | Expr.box t x        => emitBox builder z x t
  | Expr.unbox x        => emitUnbox builder z t x
  | Expr.isShared x     => emitIsShared builder z x
  | Expr.isTaggedPtr _x  => throw (Error.unimplemented "emitIsTaggedPtr z x")
  | Expr.lit v          => let _ ← emitLit builder z t v

-- ^^^ emitVDecl ^^^


/-
bollu: consider removing declareVar and declareVars, it's quite nonsensical
to have such a mechanism in a language such as LLVM.
-/
/-
def declareVar (x : VarId) (t : IRType) : M Unit := do
  emit (toCType t); emit " "; emit x; emit "; "
-/

def declareVar (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (t : IRType) : M Unit := do
  let alloca ← LLVM.buildAlloca builder (← toLLVMType t) "varx"
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

partial def declareVars (builder: LLVM.Ptr LLVM.Builder) (f: FnBody): M Unit := do
  debugPrint "declareVars"
  match f with
  | FnBody.vdecl x t _ b => do
      declareVar builder x t; declareVars builder b

  | FnBody.jdecl _ xs _ b => do
      for param in xs do declareVar builder param.x param.ty
      declareVars builder b
      -- throw (Error.unimplemented "declareVars.jdecl")
  | e => do
      if e.isTerminal then pure () else declareVars builder e.body


/-
def emitTag (x : VarId) (xType : IRType) : M Unit := do
  if xType.isObj then do
    emit "lean_obj_tag("; emit x; emit ")"
  else
    emit x
-/
def emitTag (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (xType : IRType) : M (LLVM.Ptr LLVM.Value) := do
  if xType.isObj then do
    let xval ← emitLhsVal builder x
    callLeanObjTag builder xval ""
  else if xType.isScalar then do
    -- TODO (bollu): is it correct to assume that emitLit will do the right thing
    -- if it's not an object?
    emitLhsVal builder x
  else
    throw (Error.compileError "don't know how to `emitTag` in general")

/-
def emitSet (x : VarId) (i : Nat) (y : Arg) : M Unit := do
  emit "lean_ctor_set("; emit x; emit ", "; emit i; emit ", "; emitArg y; emitLn ");"
-/
def emitSet (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (i : Nat) (y : Arg) : M Unit := do
  let ctx ← getLLVMContext
  let fnName :=  "lean_ctor_set"
  let retty ← LLVM.voidType ctx
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx, ← LLVM.voidPtrType ctx]
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let _ ← LLVM.buildCall builder fn  #[← emitLhsVal builder x, ← constIntUnsigned i, ← emitArgVal builder y]


def emitTailCall (builder: LLVM.Ptr LLVM.Builder) (v : Expr) : M Unit := do
  debugPrint "emitTailCall"
   match v with
  | Expr.fap _ ys => do
    let ctx ← read
    let ps := ctx.mainParams
    unless ps.size == ys.size do throw (Error.compileError "invalid tail call")
    -- throw (Error.unimplemented "emitTailCall")
    -- TODO (bollu): we currently sneak the notion of 'current function' to be tail called
    -- based on the IR builder state. This is Very Bad. Instead, it should be
    -- explicit in our model.
    let args ← ys.mapM (emitArgVal builder)
    let fn ← builderGetInsertionFn builder
    let call ← LLVM.buildCall builder fn args
    -- TODO (bollu): add 'musttail' attribute
    LLVM.setTailCall call true -- mark as tail call
    let _ ← LLVM.buildRet builder call
  | _ => throw (Error.compileError "bug at emitTailCall")


/-
def emitJmp (j : JoinPointId) (xs : Array Arg) : M Unit := do
  let ps ← getJPParams j
  unless xs.size == ps.size do throw "invalid goto"
  xs.size.forM fun i => do
    let p := ps[i]!
    let x := xs[i]!
    emit p.x; emit " = "; emitArg x; emitLn ";"
  emit "goto "; emit j; emitLn ";"
-/
def emitJmp (builder: LLVM.Ptr LLVM.Builder) (jp : JoinPointId) (xs : Array Arg) : M Unit := do
 let ctx ← read;
  let ps ← match ctx.jpMap.find? jp with
  | some ps => pure ps
  | none    => throw (Error.compileError "unknown join point")
  unless xs.size == ps.size do throw (Error.compileError "invalid goto")
  for (p, x)  in ps.zip xs do
    let xv ← emitArgVal builder x
    emitLhsSlotStore builder p.x xv
    -- emit p.x; emit " = "; emitArg x; emitLn ";"
  -- emit "goto "; emit j; emitLn ";"
  let _ ← LLVM.buildBr builder (← emitJp jp)

/-
def emitUSet (x : VarId) (n : Nat) (y : VarId) : M Unit := do
  emit "lean_ctor_set_usize("; emit x; emit ", "; emit n; emit ", "; emit y; emitLn ");"
-/
/-
def emitUSet (x : VarId) (n : Nat) (y : VarId) : M Unit := do
  emit "lean_ctor_set_usize("; emit x; emit ", "; emit n; emit ", "; emit y; emitLn ");"
-/


/-
def emitSSet (x : VarId) (n : Nat) (offset : Nat) (y : VarId) (t : IRType) : M Unit := do
  match t with
  | IRType.float  => emit "lean_ctor_set_float"
  | IRType.uint8  => emit "lean_ctor_set_uint8"
  | IRType.uint16 => emit "lean_ctor_set_uint16"
  | IRType.uint32 => emit "lean_ctor_set_uint32"
  | IRType.uint64 => emit "lean_ctor_set_uint64"
  | _             => throw "invalid instruction";
  emit "("; emit x; emit ", "; emitOffset n offset; emit ", "; emit y; emitLn ");"
-/
def emitSSet (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (n : Nat) (offset : Nat) (y : VarId) (t : IRType) : M Unit := do
  let ctx ← getLLVMContext
  let (fnName, setty) ←
  match t with
  | IRType.float  => pure ("lean_ctor_set_float", ← LLVM.doubleTypeInContext ctx)
  | IRType.uint8  => pure ("lean_ctor_set_uint8", ← LLVM.i8Type ctx)
  | IRType.uint16 => pure ("lean_ctor_set_uint16", ← LLVM.i16Type ctx)
  | IRType.uint32 => pure ("lean_ctor_set_uint32", ← LLVM.i32Type ctx)
  | IRType.uint64 => pure ("lean_ctor_set_uint64", ← LLVM.i64Type ctx)
  | _             => throw (Error.compileError "invalid instruction");
  let argtys := #[ ← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx, setty]
  let retty  ← LLVM.voidType ctx
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty fnName argtys
  let xv ← emitLhsVal builder x
  let offset ← emitOffset builder n offset
  let yv ← emitLhsVal builder y
  let _ ← LLVM.buildCall builder fn  #[xv, offset, yv]


/-
def emitDel (x : VarId) : M Unit := do
  emit "lean_free_object("; emit x; emitLn ");"
-/
def emitDel (builder: LLVM.Ptr LLVM.Builder) (x : VarId) : M Unit := do
  let ctx ← getLLVMContext
  let argtys := #[ ← LLVM.voidPtrType ctx]
  let retty  ← LLVM.voidType ctx
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty "lean_free_object" argtys
  let xv ← emitLhsVal builder x
  let _ ← LLVM.buildCall builder fn  #[xv]


/-
def emitSetTag (x : VarId) (i : Nat) : M Unit := do
  emit "lean_ctor_set_tag("; emit x; emit ", "; emit i; emitLn ");"
-/


def emitSetTag (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (i : Nat) : M Unit := do
  let ctx ← getLLVMContext
  let argtys := #[← LLVM.voidPtrType ctx, ← LLVM.size_tType ctx]
  let retty  ← LLVM.voidType ctx
  let fn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) retty "lean_ctor_set_tag" argtys
  let xv ← emitLhsVal builder x
  let _ ← LLVM.buildCall builder fn  #[xv, ← constIntUnsigned i]



def ensureHasDefault' (alts : Array Alt) : Array Alt :=
  if alts.any Alt.isDefault then alts
  else
    let last := alts.back;
    let alts := alts.pop;
    alts.push (Alt.default last.body)



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
partial def emitCase (builder: LLVM.Ptr LLVM.Builder) (x : VarId) (xType : IRType) (alts : Array Alt) : M Unit := do
    let oldBB ← LLVM.getInsertBlock builder
    debugPrint "emitCase"
    -- TODO: this needs to be done very carefully. I think I might need to do some sort of shenanigan to convert between 0/-1 to 0/1 ?
    let tag ← emitTag builder x xType
    let tag ← LLVM.buildZext builder tag (← LLVM.i64Type (← getLLVMContext))  ""
    -- TODO: sign extend tag into 64-bit.
    -- emit "switch ("; emitTag x xType; emitLn ") {";
    let alts := ensureHasDefault' alts;
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
         -- emit "case "; emit c.cidx; emitLn ":"; emitFnBody b
      | Alt.default b =>
         LLVM.positionBuilderAtEnd builder defaultBB
         emitFnBody builder b
         -- emitLn "default: "; emitFnBody b
    -- emitLn "}"
    -- this builder does not have an insertion position after emitting a case
    LLVM.clearInsertionPosition builder
    -- TODO(bollu): we should never need this code. Any code that wants to access the parent function
    -- should use the state that is stored in the context, and not use the implicit context of the builder.
    LLVM.positionBuilderAtEnd builder oldBB -- reset state
-- contract: emitJP will keep the builder context untouched.
partial def emitJDecl (builder: LLVM.Ptr LLVM.Builder) (jp: JoinPointId) (_ps: Array Param) (b: FnBody): M Unit := do
  let oldBB ← LLVM.getInsertBlock builder -- TODO: state saving into pattern
  let jpbb ← builderAppendBasicBlock builder s!"jp_{jp.idx}"
  addJpTostate jp jpbb
  LLVM.positionBuilderAtEnd builder jpbb
  -- TODO(bollu): this is quite subtle. Here, we declare the vars that are inside the body
  -- of the jp
  declareVars builder b
  emitBlock builder b
  LLVM.positionBuilderAtEnd builder oldBB -- reset state



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
  | FnBody.ret x               => emit "return "; emitArgSlot_ x; emitLn ";"
  | FnBody.case _ x xType alts => emitCase x xType alts
  | FnBody.jmp j xs            => emitJmp j xs
  | FnBody.unreachable         => emitLn "lean_internal_panic_unreachable();"
-/

partial def emitBlock (builder: LLVM.Ptr LLVM.Builder) (b : FnBody) : M Unit := do
  debugPrint "emitBlock"
  match b with
  | FnBody.jdecl j xs  v b      =>
       emitJDecl builder j xs v
       emitBlock builder b
  | d@(FnBody.vdecl x t v b)   => do
    -- throw (Error.unimplemented "vdecl")
    let ctx ← read
    if isTailCallTo ctx.mainFn d then
      emitTailCall builder v
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

  | FnBody.set x i y b         =>
     emitSet builder x i y; emitBlock builder b
  | FnBody.uset _x _i _y _b        => throw (Error.unimplemented "uset")
  /-
  emitUSet x i y; emitBlock b
  -/
  | FnBody.sset x i o y t b    => emitSSet builder x i o y t; emitBlock builder b
  | FnBody.mdata _ _b           =>  throw (Error.unimplemented "mdata")
  /-
  emitBlock b
  -/
  | FnBody.ret x               => do
      /-
      emit "return "; emitArgSlot_ x; emitLn ";"
      -/
      let xv ← emitArgVal builder x "ret_val"
      let _ ← LLVM.buildRet builder xv
  | FnBody.case _ x xType alts => -- throw (Error.unimplemented "case")
     emitCase builder x xType alts
  | FnBody.jmp j xs            =>
     emitJmp builder j xs
  | FnBody.unreachable         => throw (Error.unimplemented "unreachable")
  /-
  emitLn "lean_internal_panic_unreachable();"
  -/
/-
partial def emitJPs (builder: LLVM.Ptr LLVM.Builder) (body: FnBody): M Unit := do
  | FnBody.jdecl j _  v b => -- do emit j; emitLn ":"; emitFnBody v; emitJPs b
  | e                     => do unless e.isTerminal do emitJPs e.body
-/


/-
partial def emitFnBody (b : FnBody) : M Unit := do
  emitLn "{"
  let declared ←
   b false
  if declared then emitLn ""
  emitBlock b
  emitJPs b
  emitLn "}"
-/
partial def emitFnBody  (builder: LLVM.Ptr LLVM.Builder)  (b : FnBody): M Unit := do
  debugPrint "emitFnBody"
  -- let declared ← declareVars b false
  -- if declared then emitLn ""
  declareVars builder b -- This looks very dangerous to @bollu, because we are literally creating stack slots with nothing in them.

  -- emitJPs builder b

  -- emitLn "{"
  emitBlock builder b   -- emitBlock b
  -- LLVM.positionBuilderAtEnd builder bb

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


def emitFnArgs (ctx: LLVM.Ptr LLVM.Context) (builder: LLVM.Ptr LLVM.Builder) (needsPackedArgs?: Bool)  (llvmfn: LLVM.Ptr LLVM.Value) (params: Array Param) : M Unit := do
  if needsPackedArgs? then do
      -- throw (Error.unimplemented "unimplemented > closureMaxArgs case")
      let argsp ← LLVM.getParam llvmfn 0 -- lean_object **args
      for i in List.range params.size do
          let argsi ← LLVM.buildGEP builder argsp #[← constIntUnsigned i] s!"packed_arg_{i}_slot"
          let pv ← LLVM.buildLoad builder argsi
          let alloca ← LLVM.buildAlloca builder (← LLVM.voidPtrType ctx) s!"arg_{i}"
          LLVM.buildStore builder pv alloca
          addVartoState params[i]!.x alloca
  else
      let n := LLVM.countParams llvmfn
      for i in (List.range n.toNat) do
        let alloca ← LLVM.buildAlloca builder (← toLLVMType params[i]!.ty) s!"arg_{i}"
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
      let retty ← toLLVMType t
      let mut argtys := #[]
      let needsPackedArgs? := xs.size > closureMaxArgs && isBoxedName d.name
      if needsPackedArgs? then
          -- TODO: why does this not work?
          argtys := #[← LLVM.pointerType (← LLVM.voidPtrType ctx)]
      else
        for x in xs do
          argtys := argtys.push (← toLLVMType x.ty)
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
      --   xs.size.forM fun i => do
      --     let x := xs[i]!
      --     emit "lean_object* "; emit x.x; emit " = _args["; emit i; emitLn "];"
      -- emitLn "_start:";
      withReader (fun ctx => { ctx with mainFn := f, mainParams := xs }) (do
        set { var2val := default, jp2bb := default : EmitLLVM.State } -- flush varuable map
        let bb ← LLVM.appendBasicBlockInContext (← getLLVMContext) llvmfn "entry"
        LLVM.positionBuilderAtEnd builder bb
        emitFnArgs ctx builder needsPackedArgs? llvmfn xs
        emitFnBody builder b);
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
  let d := d.normalizeIds; -- ensure we don't have gaps in the variable indices
  try
    emitDeclAux ctx mod builder d
    return ()
  catch err =>
    throw (Error.unimplemented s!"emitDecl:\ncompiling:\n{d}\nerr:\n{err}\na")

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
  let ctx ← getLLVMContext
  let env ← getEnv
  let n := d.name
  if isIOUnitInitFn env n then do
    -- emit "res = "; emitCName n; emitLn "(lean_io_mk_world());"
    -- emitLn "if (lean_io_result_is_error(res)) return res;"
    -- emitLn "lean_dec_ref(res);"
    let world ← callLeanIOMkWorld builder
    let initf ← getOrCreateFunctionPrototype ctx (← getLLVMModule) (← toLLVMType d.resultType) (← toCName n)
                #[← LLVM.i8Type ctx, ← LLVM.voidPtrType ctx]
    let resv ← LLVM.buildCall builder initf #[world]
    let err? ← callLeanIOResultIsError builder resv "is_error"
    buildIfThen_ builder s!"init_{d.name}_isError" err?
      (fun builder => do
        let _ ← LLVM.buildRet builder resv
        pure ShouldForwardControlFlow.no)
    -- TODO (bollu): emit lean_dec_ref. For now, it does not matter.
  else if d.params.size == 0 then
    match getInitFnNameFor? env d.name with
    | some initFn =>
      let llvmty ← toLLVMType d.resultType
      let dslot ←  LLVM.getOrAddGlobal (← getLLVMModule) (← toCName n) llvmty
      LLVM.setInitializer dslot (← LLVM.getUndef llvmty)
      -- build slot for d
      let initBB ← builderAppendBasicBlock builder s!"do_{d.name}_init"
      let restBB ← builderAppendBasicBlock builder s!"post_{d.name}_init"
      let checkBuiltin? := getBuiltinInitFnNameFor? env d.name |>.isSome
      if checkBuiltin? then
         -- TODO (bollu): what does this condition mean?
        let builtinParam ← LLVM.getParam parentFn 0 -- TODO(bollu): what does this argument mean?
        let cond ← buildLeanBoolTrue? builder builtinParam "is_builtin_true"
        let _ ← LLVM.buildCondBr builder cond initBB restBB
       else
        let _ ← LLVM.buildBr builder initBB

      -- vvfill in initvv
      LLVM.positionBuilderAtEnd builder initBB
      let dInitFn ← getOrCreateFunctionPrototype ctx (← getLLVMModule) (← toLLVMType d.resultType) (← toCName initFn)
        #[← LLVM.i8Type ctx, ← LLVM.voidPtrType ctx]
      let world ← callLeanIOMkWorld builder
      let resv ← LLVM.buildCall builder dInitFn #[world]
      -- TODO(bollu): eliminate code duplication
      let err? ← callLeanIOResultIsError builder resv s!"{d.name}_is_error"
      buildIfThen_ builder s!"init_{d.name}_isError" err?
        (fun builder => do
          let _ ← LLVM.buildRet builder resv
          pure ShouldForwardControlFlow.no)
      let dval ← callLeanIOResultGetValue builder resv s!"{d.name}_res"
      LLVM.buildStore builder dval dslot
      if d.resultType.isObj then
         callLeanMarkPersistentFn builder dval
      let _ ← LLVM.buildBr builder restBB
      -- ^^end filling up of init.^^
      LLVM.positionBuilderAtEnd builder restBB

    | _ => do
          -- emitCName n; emit " = "; emitCInitName n; emitLn "();"; emitMarkPersistent d n
      -- TODO: should this be global?
      let llvmty ← toLLVMType d.resultType
      let dslot ←  LLVM.getOrAddGlobal (← getLLVMModule) (← toCName n) llvmty
      LLVM.setInitializer dslot (← LLVM.getUndef llvmty)
      -- TODO (bollu): this should probably be getOrCreateNamedFunction
      let dInitFn ← match (← LLVM.getNamedFunction (← getLLVMModule) (←  toCInitName n)) with
                    | .some dInitFn => pure dInitFn
                    | .none => throw (Error.compileError s!"unable to find function {← toCInitName n}")
      let dval ← LLVM.buildCall builder dInitFn #[] ""
      LLVM.buildStore builder dval dslot
       /-
       def emitMarkPersistent (d : Decl) (n : Name) : M Unit := do
          if d.resultType.isObj then
             emit "lean_mark_persistent("
            emitCName n
            emitLn ");"
      -/
      if d.resultType.isObj then
         callLeanMarkPersistentFn builder dval


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
  let ginit?slot ← LLVM.getOrAddGlobal mod (modName.mangle ++ "_G_initialized") (← LLVM.i1Type ctx)
  LLVM.setInitializer ginit?slot (← LLVM.False ctx)
  let ginit?v ← LLVM.buildLoad builder ginit?slot "init_v"
  buildIfThen_ builder "isGInitialized" ginit?v
    (fun builder => do
      let box0 ← callLeanBox builder (← LLVM.constIntUnsigned ctx 0) "box0"
      let out ← callLeanIOResultMKOk builder box0 "retval"
      let _ ← LLVM.buildRet builder out
      pure ShouldForwardControlFlow.no)
  LLVM.buildStore builder (← LLVM.True ctx) ginit?slot

  /-
  env.imports.forM fun imp => emitLns [
    "res = " ++ mkModuleInitializationFunctionName imp.module ++ "(builtin, lean_io_mk_world());",
    "if (lean_io_result_is_error(res)) return res;",
    "lean_dec_ref(res);"]
  -/
  env.imports.forM fun import_ => do
    let importFnTy ← LLVM.functionType (← LLVM.voidPtrType ctx) #[ (← LLVM.i8Type ctx), (← LLVM.voidPtrType ctx)]
    let importInitFn ← LLVM.getOrAddFunction mod (mkModuleInitializationFunctionName import_.module) importFnTy
    let builtin ← LLVM.getParam initFn 0
    let world ← callLeanIOMkWorld builder
    let res ← LLVM.buildCall builder importInitFn #[builtin, world] ("res_" ++ import_.module.mangle)
    let err? ← callLeanIOResultIsError builder res ("res_is_error_"  ++ import_.module.mangle)
    buildIfThen_ builder ("IsError" ++ import_.module.mangle) err?
      (fun builder => do
        let _ ← LLVM.buildRet builder res
        pure ShouldForwardControlFlow.no)
    callLeanDecRef builder res
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
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidType ctx) "lean_initialize"  #[]

def getOrCreateLeanInitializeRuntimeModule (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- void lean_initialize();
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidType ctx) "lean_initialize_runtime_module"  #[]

def getOrCreateLeanSetPanicMessages (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  -- void lean_set_panic_messages();
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidType ctx) "lean_set_panic_messages"  #[(← LLVM.i1Type ctx)]


def getOrCreateLeanIOMarkEndInitializationFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  getOrCreateFunctionPrototype ctx mod (← LLVM.voidType ctx) "lean_io_mark_end_initialization"  #[]

-- bool lean_io_result_is_ok (void *) --
def getOrCreateLeanIOResultIsOkFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module): M (LLVM.Ptr LLVM.Value) := do
  getOrCreateFunctionPrototype ctx mod (← LLVM.i1Type ctx) "lean_io_result_is_ok"  #[(← LLVM.voidPtrType ctx)]

def callLeanIOResultIsOk (builder: LLVM.Ptr LLVM.Builder) (arg: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
  LLVM.buildCall builder (← getOrCreateLeanIOResultIsOkFn (← getLLVMContext) (← getLLVMModule)) #[arg] name




-- lean_init_task_manager
def getOrCreateLeanInitTaskManagerFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidType ctx) "lean_init_task_manager"  #[]


def callLeanInitTaskManager (builder: LLVM.Ptr LLVM.Builder): M Unit := do
   let _ ← LLVM.buildCall builder (← getOrCreateLeanInitTaskManagerFn) #[] ""


def getOrCreateLeanFinalizeTaskManager: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidType ctx) "lean_finalize_task_manager"  #[]


def callLeanFinalizeTaskManager (builder: LLVM.Ptr LLVM.Builder): M Unit := do
   let _ ← LLVM.buildCall builder (← getOrCreateLeanFinalizeTaskManager) #[] ""

def getOrCreateCallLeanUnboxUint32Fn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.i32Type ctx) "lean_unbox_uint32"  #[← LLVM.voidPtrType ctx]


def callLeanUnboxUint32 (builder: LLVM.Ptr LLVM.Builder) (v: LLVM.Ptr LLVM.Value) (name: String): M (LLVM.Ptr LLVM.Value) := do
   LLVM.buildCall builder (← getOrCreateCallLeanUnboxUint32Fn) #[v] name



-- ***lean_io_result_show_error**
def getOrCreateLeanIOResultShowErrorFn: M (LLVM.Ptr LLVM.Value) := do
  let ctx ← getLLVMContext
  getOrCreateFunctionPrototype ctx (← getLLVMModule)
    (← LLVM.voidType ctx) "lean_io_result_show_error"  #[← LLVM.voidPtrType ctx]

def callLeanIOResultShowError (builder: LLVM.Ptr LLVM.Builder) (v: LLVM.Ptr LLVM.Value) (name: String): M Unit := do
   let _ ← LLVM.buildCall builder (← getOrCreateLeanIOResultShowErrorFn) #[v] name




def emitMainFn (ctx: LLVM.Ptr LLVM.Context) (mod: LLVM.Ptr LLVM.Module) (builder: LLVM.Ptr LLVM.Builder): M Unit := do
  let d ← getDecl `main
  let xs ← match d with
   | .fdecl (xs := xs) .. => pure xs
   | _ =>  throw (Error.compileError "function declaration expected")
  debugPrint s!"emitMainFn xs.size {xs.size}"

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
  let mainTy ← LLVM.functionType (← LLVM.i64Type ctx)
      #[(← LLVM.i64Type ctx), (← LLVM.pointerType (← LLVM.voidPtrType ctx))]
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
  let inslot ← LLVM.buildAlloca builder (← LLVM.i8PtrType ctx) "in"
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
  let modInitFnTy ← LLVM.functionType (← LLVM.voidPtrType ctx) #[ (← LLVM.i8Type ctx), (← LLVM.voidPtrType ctx)]
  let modInitFn ← LLVM.getOrAddFunction mod (mkModuleInitializationFunctionName modName) modInitFnTy
  let _ ← LLVM.buildCall builder setPanicMesagesFn #[(← LLVM.False ctx )] ""
  let world ← callLeanIOMkWorld builder
  let resv ← LLVM.buildCall builder modInitFn #[(← LLVM.constInt8 ctx 1 ), world] (modName.toString ++ "_init_out")
  let _ ← LLVM.buildStore builder resv res

  let _ ← LLVM.buildCall builder setPanicMesagesFn #[(← LLVM.True ctx )] ""
  let _ ← LLVM.buildCall builder (← getOrCreateLeanIOMarkEndInitializationFn ctx mod) #[] ""

  let resv ← LLVM.buildLoad builder res "resv"
  let res_is_ok ← callLeanIOResultIsOk builder resv "res_is_ok"
  buildIfThen_ builder "resIsOkBranches"  res_is_ok
    (fun builder => do -- then clause of the builder)
      callLeanDecRef builder resv
      callLeanInitTaskManager builder
      if xs.size == 2 then
        let inv ← callLeanBox builder (← LLVM.constInt (← LLVM.size_tType ctx) 0) "inv"
        let _ ← LLVM.buildStore builder inv inslot
        let islot ← LLVM.buildAlloca builder  (← LLVM.size_tType ctx) "islot"
        let argcval ← LLVM.getParam main 0
        let argvval ← LLVM.getParam main 1
        LLVM.buildStore builder argcval islot
        buildWhile_ builder "argv"
          (condcodegen := fun builder => do
            let iv ← LLVM.buildLoad builder islot "iv"
            let i_gt_1 ← LLVM.buildICmp builder LLVM.IntPredicate.UGT iv (← constIntUnsigned 1) "i_gt_1"
            return i_gt_1)
          (bodycodegen := fun builder => do
            let iv ← LLVM.buildLoad builder islot "iv"
            let iv_next ← LLVM.buildSub builder iv (← constIntUnsigned 1) "iv.next"
            LLVM.buildStore builder iv_next islot
            let nv ← callLeanAllocCtor builder 1 2 0 "nv"
            let argv_i_next_slot ← LLVM.buildGEP builder argvval #[iv_next] "argv.i.next.slot"
            let argv_i_next_val ← LLVM.buildLoad builder argv_i_next_slot "argv.i.next.val"
            let argv_i_next_val_str ← callLeanMkString builder argv_i_next_val "arg.i.next.val.str"
            let _ ← callLeanCtorSet builder nv (← constIntUnsigned 0) argv_i_next_val_str
            let inv ← LLVM.buildLoad builder inslot "inv"
            let _ ← callLeanCtorSet builder nv (← constIntUnsigned 1) inv
            LLVM.buildStore builder nv inslot)
        let leanMainFnTy ← LLVM.functionType (← LLVM.voidPtrType ctx) #[(← LLVM.voidPtrType ctx), (← LLVM.voidPtrType ctx)]
        let leanMainFn ← LLVM.getOrAddFunction mod leanMainFn leanMainFnTy
        let world ← callLeanIOMkWorld builder
        let inv ← LLVM.buildLoad builder inslot "inv"
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
        let retv ← LLVM.buildSext builder retv (← LLVM.i64Type ctx) "retv_sext"
        callLeanDecRef builder resv
        let _ ← LLVM.buildRet builder retv
        pure ShouldForwardControlFlow.no
      else do
        callLeanDecRef builder resv
        let _ ← LLVM.buildRet builder (← LLVM.constInt64 ctx 0)
        pure ShouldForwardControlFlow.no

    )
    (fun builder => do -- else builder
        let resv ← LLVM.buildLoad builder res "resv"
        callLeanIOResultShowError builder resv ""
        callLeanDecRef builder resv
        let _ ← LLVM.buildRet builder (← LLVM.constInt64 ctx 1)
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


-- This imitates `Lean/Util/Path.lean`, implementing `Lean.getLibDir`
open System in
def getLibLeanRtPath : IO FilePath := do
  let mut buildDir ← getBuildDir
  -- use stage1 stdlib with stage0 executable (which should never be distributed outside of the build directory)
  if Internal.isStage0 () then
    buildDir := buildDir / ".." / "stage1"
  return buildDir / "runtime" / "libleanrt.bc"


-- | TODO: Use a beter type signature than this.
-- | TODO: produce bitcode instead of an LLVM string.
@[export lean_ir_emit_llvm]
def emitLLVM (env : Environment) (modName : Name) (filepath: String): IO Unit := do
  let llvmctx ← LLVM.createContext
  let module ← LLVM.createModule llvmctx modName.toString -- TODO: pass module name
  let ctx := {env := env, modName := modName, llvmctx := llvmctx, llvmmodule := module}
  let initState := { var2val := default, jp2bb := default : EmitLLVM.State}
  let out? ← (EmitLLVM.main initState ctx).run
  match out? with
  | .ok _ => do
         let membuf ← LLVM.createMemoryBufferWithContentsOfFile (← getLibLeanRtPath).toString
         let modruntime ← LLVM.parseBitcode llvmctx membuf
         -- TODO (bollu): mark everything in runtime as internal and alwaysinline
         -- so we can then remove the
         -- unused portions after inlining
         LLVM.linkModules (dest := ctx.llvmmodule) (src := modruntime)
         LLVM.printModuletoFile ctx.llvmmodule "/home/bollu/temp/lean-llvm.linked.ll"
         -- TODO (bollu): run pass pipeline
         LLVM.writeBitcodeToFile ctx.llvmmodule filepath
         -- TODO (bollu): produce object code directly.
         -- https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/LangImpl08.html
         let tripleStr ← LLVM.getDefaultTargetTriple
         let target ← LLVM.getTargetFromTriple tripleStr
         let cpu := "generic"
         let features := ""
         let targetmachine ← LLVM.createTargetMachine target tripleStr cpu features
         -- TheModule->setDataLayout(TargetMachine->createDataLayout());
         -- TheModule->setTargetTriple(TargetTriple);
         let codegenType := LLVM.CodeGenFileType.ObjectFile
         LLVM.targetMachineEmitToFile targetmachine ctx.llvmmodule (filepath ++ ".o") codegenType

  | .error err => IO.eprintln ("ERROR: " ++ toString err); return () -- throw (IO.userError <| toString err)
end Lean.IR
