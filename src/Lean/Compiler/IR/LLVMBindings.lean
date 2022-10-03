/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

namespace LLVM

namespace CodeGenFileType
def AssemblyFile : UInt64 := 0
def ObjectFile : UInt64 := 1
end CodeGenFileType

namespace IntPredicate
-- https://llvm.org/doxygen/group__LLVMCCoreTypes.html#ga79d2c730e287cc9cf6410d8b24880ce6
def EQ : UInt64 := 32
def NE : UInt64 := EQ + 1
def UGT : UInt64 := NE + 1
end IntPredicate

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
structure MemoryBuffer where
structure Target where
structure TargetMachine where

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

@[extern "lean_llvm_build_global_string"]
opaque buildGlobalString(builder: @&Ptr Builder) (value: @&String) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_set_initializer"]
opaque setInitializer (glbl: @&Ptr Value) (val: @&Ptr Value): IO Unit

@[extern "lean_llvm_function_type"]
opaque functionType(retty: @&Ptr LLVMType) (args: @&Array (Ptr LLVMType)) (isVarArg: Bool := false): IO (Ptr LLVMType)

@[extern "lean_llvm_void_type_in_context"]
opaque voidType (ctx: @&Ptr Context): IO (Ptr LLVMType)

@[extern "lean_llvm_int_type_in_context"]
opaque intTypeInContext (ctx: @&Ptr Context) (width: UInt64): IO (Ptr LLVMType)

@[extern "lean_llvm_float_type_in_context"]
opaque floatType (ctx: @&Ptr Context): IO (Ptr LLVMType)

@[extern "lean_llvm_double_type_in_context"]
opaque doubleTypeInContext (ctx: @&Ptr Context): IO (Ptr LLVMType)

@[extern "lean_llvm_pointer_type"]
opaque pointerType (elemty: @&Ptr LLVMType): IO (Ptr LLVMType)

@[extern "lean_llvm_array_type"]
opaque arrayType (elemty: @&Ptr LLVMType) (nelem: @&UInt64): IO (Ptr LLVMType)

@[extern "lean_llvm_const_array"]
opaque constArray (elemty: @&Ptr LLVMType) (vals: @&Array (Ptr Value)): IO (Ptr LLVMType)

-- `constString` provides a `String` as a constant array of element type `i8`
@[extern "lean_llvm_const_string"]
opaque constString (ctx: @&Ptr Context) (str: @&String): IO (Ptr Value)

@[extern "lean_llvm_const_pointer_null"]
opaque constPointerNull (elemTy: @&Ptr LLVMType): IO (Ptr Value)

@[extern "lean_llvm_get_undef"]
opaque getUndef (elemTy: @&Ptr LLVMType): IO (Ptr Value)

@[extern "lean_llvm_create_builder_in_context"]
opaque createBuilderInContext (ctx: @&Ptr Context): IO (Ptr Builder)

@[extern "lean_llvm_append_basic_block_in_context"]
opaque appendBasicBlockInContext (ctx: @&Ptr Context) (fn: @& Ptr Value) (name:  @&String): IO (Ptr BasicBlock)

@[extern "lean_llvm_position_builder_at_end"]
opaque positionBuilderAtEnd (builder: @&Ptr Builder) (bb: @& Ptr BasicBlock): IO Unit

-- @[extern "lean_llvm_build_call2"]
-- opaque buildCall2 (builder: @&Ptr Builder) (fnty: @&Ptr LLVMType) (fn: @&Ptr Value) (args: @&Array (Ptr Value)) (name: @&String): IO (Ptr Value)

@[extern "lean_llvm_build_call"]
opaque buildCall (builder: @&Ptr Builder) (fn: @&Ptr Value) (args: @&Array (Ptr Value)) (name:  @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_set_tail_call"]
opaque setTailCall (fn: @&Ptr Value) (isTail: Bool): IO Unit

@[extern "lean_llvm_build_cond_br"]
opaque buildCondBr (builder: @&Ptr Builder) (if_: @&Ptr Value) (thenbb: @&Ptr BasicBlock) (elsebb: @&Ptr BasicBlock): IO (Ptr Value)

@[extern "lean_llvm_build_br"]
opaque buildBr (builder: @&Ptr Builder) (bb: @&Ptr BasicBlock): IO (Ptr Value)

@[extern "lean_llvm_build_alloca"]
opaque buildAlloca (builder: @&Ptr Builder) (ty: @&Ptr LLVMType) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_load"]
opaque buildLoad (builder: @&Ptr Builder) (val: @&Ptr Value) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_store"]
opaque buildStore (builder: @&Ptr Builder) (val: @&Ptr Value) (store_loc_ptr: @&Ptr Value): IO Unit

@[extern "lean_llvm_build_ret"]
opaque buildRet (builder: @&Ptr Builder) (val: @&Ptr Value): IO (Ptr Value)

@[extern "lean_llvm_build_unreachable"]
opaque buildUnreachable (builder: @&Ptr Builder): IO (Ptr Value)

@[extern "lean_llvm_build_gep"]
opaque buildGEP (builder: @&Ptr Builder) (base: @&Ptr Value) (ixs: @&Array (Ptr Value)) (name: @&String := ""): IO (Ptr Value)


@[extern "lean_llvm_build_inbounds_gep"]
opaque buildInBoundsGEP (builder: @&Ptr Builder) (base: @&Ptr Value) (ixs: @&Array (Ptr Value)) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_pointer_cast"]
opaque buildPointerCast (builder: @&Ptr Builder) (val: @&Ptr Value) (destTy: @&Ptr LLVMType) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_sext"]
opaque buildSext (builder: @&Ptr Builder) (val: @&Ptr Value) (destTy: @&Ptr LLVMType) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_zext"]
opaque buildZext (builder: @&Ptr Builder) (val: @&Ptr Value) (destTy: @&Ptr LLVMType) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_sext_or_trunc"]
opaque buildSextOrTrunc (builder: @&Ptr Builder) (val: @&Ptr Value) (destTy: @&Ptr LLVMType) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_switch"]
opaque buildSwitch (builder: @&Ptr Builder) (val: @&Ptr Value) (elseBB: @&Ptr BasicBlock) (numCasesHint: @&UInt64): IO (Ptr Value)

@[extern "lean_llvm_build_ptr_to_int"]
opaque buildPtrToInt (builder: @&Ptr Builder) (ptr: @&Ptr Value) (destTy: @&Ptr LLVMType) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_mul"]
opaque buildMul (builder: @&Ptr Builder) (x y: @&Ptr Value) (name: @&String): IO (Ptr Value)

@[extern "lean_llvm_build_add"]
opaque buildAdd (builder: @&Ptr Builder) (x y: @&Ptr Value) (name: @&String): IO (Ptr Value)

@[extern "lean_llvm_build_sub"]
opaque buildSub (builder: @&Ptr Builder) (x y: @&Ptr Value) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_not"]
opaque buildNot (builder: @&Ptr Builder) (x: @&Ptr Value) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_build_icmp"]
opaque buildICmp (builder: @&Ptr Builder) (predicate: UInt64) (x y: @&Ptr Value) (name: @&String := ""): IO (Ptr Value)

@[extern "lean_llvm_add_case"]
opaque addCase (switch onVal: @&Ptr Value) (destBB: @&Ptr BasicBlock): IO Unit

@[extern "lean_llvm_get_insert_block"]
opaque getInsertBlock (builder: @&Ptr Builder): IO (Ptr BasicBlock)

@[extern "lean_llvm_clear_insertion_position"]
opaque clearInsertionPosition (builder: @&Ptr Builder): IO Unit

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

@[extern "lean_llvm_create_memory_buffer_with_contents_of_file"]
opaque createMemoryBufferWithContentsOfFile (path: @&String): IO (Ptr MemoryBuffer)

@[extern "lean_llvm_parse_bitcode"]
opaque parseBitcode (context: @&Ptr Context) (membuf: @&Ptr MemoryBuffer): IO (Ptr Module)

@[extern "lean_llvm_link_modules"]
opaque linkModules (dest: @Ptr Module) (src: @&Ptr Module): IO Unit

@[extern "lean_llvm_get_default_target_triple"]
opaque getDefaultTargetTriple: IO String

@[extern "lean_llvm_get_target_from_triple"]
opaque getTargetFromTriple (triple: @&String): IO (Ptr Target)

@[extern "lean_llvm_create_target_machine"]
opaque createTargetMachine (target: @&Ptr Target) (tripleStr: @&String) (cpu: @&String) (features: @&String): IO (Ptr TargetMachine)

@[extern "lean_llvm_target_machine_emit_to_file"]
opaque targetMachineEmitToFile (targetMachine: @&Ptr TargetMachine) (module: @&Ptr Module) (filepath: @&String) (codegenType: @&UInt64): IO Unit


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

def i16Type (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  LLVM.intTypeInContext ctx 16

def i32Type (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  LLVM.intTypeInContext ctx 32


def i64Type (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  LLVM.intTypeInContext ctx 64

def voidPtrType (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) :=
  do LLVM.pointerType (← LLVM.intTypeInContext ctx 8)

def i8PtrType (ctx: LLVM.Ptr LLVM.Context): IO (LLVM.Ptr LLVM.LLVMType) := voidPtrType ctx

-- TODO: instantiate target triple and find out what size_t is.
def size_tType (ctx: @&Ptr Context): IO (Ptr LLVMType) := i64Type ctx

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

def constInt32 (ctx: Ptr Context) (value: UInt64) (signExtend: Bool := false): IO (Ptr Value) :=
  constInt' ctx 32 value signExtend

def constInt64 (ctx: Ptr Context) (value: UInt64) (signExtend: Bool := false): IO (Ptr Value) :=
  constInt' ctx 64 value signExtend

def constIntUnsigned (ctx: Ptr Context) (value: UInt64) (signExtend: Bool := false): IO (Ptr Value) :=
  constInt' ctx 64 value signExtend

end LLVM
