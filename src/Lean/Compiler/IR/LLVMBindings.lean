/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

namespace LLVM
/-!
This file defines bindings for LLVM. The main mechanisms
are to:
- Mirror the values of C enumerations.
- Create opaque values for LLVM's pointer based API
- Write bindings that are `IO` based, which mutate the underlying in-memory
  data structures to build IR.
-/

-- https://github.com/llvm/llvm-project/blob/c3e073bcbdc523b0f758d44a89a6333e38bff863/llvm/include/llvm-c/TargetMachine.h#L64
structure CodegenFileType where
  private mk :: val : UInt64

def CodegenFileType.AssemblyFile : CodegenFileType := { val := 0 }
def CodegenFileType.ObjectFile : CodegenFileType := { val := 1 }

-- https://github.com/llvm/llvm-project/blob/c3e073bcbdc523b0f758d44a89a6333e38bff863/llvm/include/llvm-c/Core.h#L290
structure IntPredicate where
  private mk :: val : UInt64

def IntPredicate.EQ : IntPredicate := { val := 32 }
def IntPredicate.NE : IntPredicate := { val := IntPredicate.EQ.val + 1 }
def IntPredicate.UGT : IntPredicate := { val := IntPredicate.NE.val + 1 }

-- https://github.com/llvm/llvm-project/blob/c3e073bcbdc523b0f758d44a89a6333e38bff863/llvm/include/llvm-c/Core.h#L457
structure AttributeIndex where
  private mk :: val : UInt64

def AttributeIndex.AttributeReturnIndex : AttributeIndex := { val := 0 }
-- This value is ~0 for 64 bit
def AttributeIndex.AttributeFunctionIndex : AttributeIndex := { val := 18446744073709551615 }

structure BasicBlock (ctx : Context)  where
  private mk :: ptr : USize
instance : Nonempty (BasicBlock ctx) := ⟨{ ptr := default }⟩

structure Builder (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (Builder ctx) := ⟨{ ptr := default }⟩

structure Context where
  private mk :: ptr : USize
instance : Nonempty Context := ⟨{ ptr := default }⟩

structure LLVMType (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (LLVMType ctx) := ⟨{ ptr := default }⟩

structure MemoryBuffer (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (MemoryBuffer ctx) := ⟨{ ptr := default }⟩

structure Module (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (Module ctx) := ⟨{ ptr := default }⟩

structure PassManager (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (PassManager ctx) := ⟨{ ptr := default }⟩

structure PassManagerBuilder (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (PassManagerBuilder ctx) := ⟨{ ptr := default }⟩

structure Target (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (Target ctx) := ⟨{ ptr := default }⟩

structure TargetMachine (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (TargetMachine ctx) := ⟨{ ptr := default }⟩

structure Value (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (Value ctx) := ⟨{ ptr := default }⟩

/-- Check if the value is a null pointer. --/
def Value.isNull (v : Value ctx) : Bool := v.ptr == 0

@[extern "lean_llvm_get_value_name2"]
opaque Value.getName {ctx : Context} (value : Value ctx) : BaseIO String

structure Attribute (ctx : Context) where
  private mk :: ptr : USize
instance : Nonempty (Attribute ctx) := ⟨{ ptr := default }⟩

@[extern "lean_llvm_initialize_target_info"]
opaque llvmInitializeTargetInfo : BaseIO (Unit)

@[extern "lean_llvm_create_context"]
opaque createContext : BaseIO (Context)

@[extern "lean_llvm_create_module"]
opaque createModule (ctx : Context) (name : @&String) : BaseIO (Module ctx)

@[extern "lean_llvm_module_to_string"]
opaque moduleToString (m : Module ctx) : BaseIO String

@[extern "lean_llvm_write_bitcode_to_file"]
opaque writeBitcodeToFile (m : Module ctx) (path : @&String) : BaseIO Unit

@[extern "lean_llvm_add_function"]
opaque addFunction (m : Module ctx) (name : @&String) (type : LLVMType ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_get_first_function"]
opaque getFirstFunction (m : Module ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_get_next_function"]
opaque getNextFunction (glbl : Value ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_get_named_function"]
opaque getNamedFunction (m : Module ctx) (name : @&String) : BaseIO (Option (Value ctx))

@[extern "lean_llvm_add_global"]
opaque addGlobal (m : Module ctx) (name : @&String) (type : LLVMType ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_get_named_global"]
opaque getNamedGlobal (m : Module ctx) (name : @&String) : BaseIO (Option (Value ctx))

@[extern "lean_llvm_get_first_global"]
opaque getFirstGlobal (m : Module ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_get_next_global"]
opaque getNextGlobal (glbl : Value ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_build_global_string"]
opaque buildGlobalString (builder : Builder ctx) (value : @&String) (name : @&String := "") : BaseIO (Value ctx)

@[extern "llvm_is_declaration"]
opaque isDeclaration (global : Value ctx) : BaseIO Bool

@[extern "lean_llvm_set_initializer"]
opaque setInitializer (glbl : Value ctx) (val : Value ctx) : BaseIO Unit

@[extern "lean_llvm_function_type"]
opaque functionType (retty : LLVMType ctx) (args : @&Array (LLVMType ctx)) (isVarArg : Bool := false) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_void_type_in_context"]
opaque voidType (ctx : Context) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_int_type_in_context"]
opaque intTypeInContext (ctx : Context) (width : UInt64) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_opaque_pointer_type_in_context"]
opaque opaquePointerTypeInContext (ctx : Context) (addrspace: UInt64 := 0) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_float_type_in_context"]
opaque floatTypeInContext (ctx : Context) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_double_type_in_context"]
opaque doubleTypeInContext (ctx : Context) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_pointer_type"]
opaque pointerType (elemty : LLVMType ctx) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_array_type"]
opaque arrayType (elemty : LLVMType ctx) (nelem : UInt64) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_const_array"]
opaque constArray (elemty : LLVMType ctx) (vals : @&Array (Value ctx)) : BaseIO (LLVMType ctx)

-- `constString` provides a `String` as a constant array of element type `i8`
@[extern "lean_llvm_const_string"]
opaque constString (ctx : Context) (str : @&String) : BaseIO (Value ctx)

@[extern "lean_llvm_const_pointer_null"]
opaque constPointerNull (elemty : LLVMType ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_get_undef"]
opaque getUndef (elemty : LLVMType ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_create_builder_in_context"]
opaque createBuilderInContext (ctx : Context) : BaseIO (Builder ctx)

@[extern "lean_llvm_append_basic_block_in_context"]
opaque appendBasicBlockInContext (ctx : Context) (fn :  Value ctx) (name :  @&String) : BaseIO (BasicBlock ctx)

@[extern "lean_llvm_position_builder_at_end"]
opaque positionBuilderAtEnd (builder : Builder ctx) (bb :  BasicBlock ctx) : BaseIO Unit

@[extern "lean_llvm_build_call2"]
opaque buildCall2 (builder : Builder ctx) (ty: LLVMType ctx) (fn : Value ctx) (args : @&Array (Value ctx)) (name :  @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_set_tail_call"]
opaque setTailCall (fn : Value ctx) (istail : Bool) : BaseIO Unit

@[extern "lean_llvm_build_cond_br"]
opaque buildCondBr (builder : Builder ctx) (if_ : Value ctx) (thenbb : BasicBlock ctx) (elsebb : BasicBlock ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_build_br"]
opaque buildBr (builder : Builder ctx) (bb : BasicBlock ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_build_alloca"]
opaque buildAlloca (builder : Builder ctx) (ty : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_load2"]
opaque buildLoad2 (builder : Builder ctx) (ty: LLVMType ctx) (val : Value ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_store"]
opaque buildStore (builder : Builder ctx) (val : Value ctx) (store_loc_ptr : Value ctx) : BaseIO Unit

@[extern "lean_llvm_build_ret"]
opaque buildRet (builder : Builder ctx) (val : Value ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_build_unreachable"]
opaque buildUnreachable (builder : Builder ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_build_gep2"]
opaque buildGEP2 (builder : Builder ctx) (ty: LLVMType ctx) (base : Value ctx) (ixs : @&Array (Value ctx)) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_inbounds_gep2"]
opaque buildInBoundsGEP2 (builder : Builder ctx) (ty: LLVMType ctx) (base : Value ctx) (ixs : @&Array (Value ctx)) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_sext"]
opaque buildSext (builder : Builder ctx) (val : Value ctx) (destTy : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_zext"]
opaque buildZext (builder : Builder ctx) (val : Value ctx) (destTy : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_sext_or_trunc"]
opaque buildSextOrTrunc (builder : Builder ctx) (val : Value ctx) (destTy : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_switch"]
opaque buildSwitch (builder : Builder ctx) (val : Value ctx) (elseBB : BasicBlock ctx) (numCasesHint : UInt64) : BaseIO (Value ctx)

@[extern "lean_llvm_build_ptr_to_int"]
opaque buildPtrToInt (builder : Builder ctx) (ptr : Value ctx) (destTy : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_mul"]
opaque buildMul (builder : Builder ctx) (x y : Value ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_add"]
opaque buildAdd (builder : Builder ctx) (x y : Value ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_sub"]
opaque buildSub (builder : Builder ctx) (x y : Value ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_not"]
opaque buildNot (builder : Builder ctx) (x : Value ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_build_icmp"]
opaque buildICmp (builder : Builder ctx) (predicate : IntPredicate) (x y : Value ctx) (name : @&String := "") : BaseIO (Value ctx)

@[extern "lean_llvm_add_case"]
opaque addCase (switch onVal : Value ctx) (destBB : BasicBlock ctx) : BaseIO Unit

@[extern "lean_llvm_get_insert_block"]
opaque getInsertBlock (builder : Builder ctx) : BaseIO (BasicBlock ctx)

@[extern "lean_llvm_clear_insertion_position"]
opaque clearInsertionPosition (builder : Builder ctx) : BaseIO Unit

@[extern "lean_llvm_get_basic_block_parent"]
opaque getBasicBlockParent (bb : BasicBlock ctx) : BaseIO (Value ctx)

@[extern "lean_llvm_type_of"]
opaque typeOf (val : Value ctx) : BaseIO (LLVMType ctx)

@[extern "lean_llvm_const_int"]
opaque constInt (intty : LLVMType ctx) (value : UInt64) (signExtend : @Bool := false) : BaseIO (Value ctx)

@[extern "lean_llvm_print_module_to_string"]
opaque printModuletoString (mod : Module ctx) : BaseIO (String)

@[extern "lean_llvm_print_module_to_file"]
opaque printModuletoFile (mod : Module ctx) (file : @&String) : BaseIO Unit

@[extern "llvm_count_params"]
opaque countParams (fn : Value ctx) : BaseIO UInt64

@[extern "llvm_get_param"]
opaque getParam (fn : Value ctx) (ix : UInt64) : BaseIO (Value ctx)

@[extern "lean_llvm_create_memory_buffer_with_contents_of_file"]
opaque createMemoryBufferWithContentsOfFile (path : @&String) : BaseIO (MemoryBuffer ctx)

@[extern "lean_llvm_parse_bitcode"]
opaque parseBitcode (ctx : Context) (membuf : MemoryBuffer ctx) : BaseIO (Module ctx)

@[extern "lean_llvm_link_modules"]
opaque linkModules (dest : Module ctx) (src : Module ctx) : BaseIO Unit

@[extern "lean_llvm_get_default_target_triple"]
opaque getDefaultTargetTriple : BaseIO String

@[extern "lean_llvm_get_target_from_triple"]
opaque getTargetFromTriple (triple : @&String) : BaseIO (Target ctx)

@[extern "lean_llvm_create_target_machine"]
opaque createTargetMachine (target : Target ctx) (tripleStr : @&String) (cpu : @&String) (features : @&String) : BaseIO (TargetMachine ctx)

@[extern "lean_llvm_target_machine_emit_to_file"]
opaque targetMachineEmitToFile (targetMachine : TargetMachine ctx) (module : Module ctx) (filepath : @&String) (codegenType : LLVM.CodegenFileType) : BaseIO Unit

@[extern "lean_llvm_create_pass_manager"]
opaque createPassManager : BaseIO (PassManager ctx)

@[extern "lean_llvm_dispose_pass_manager"]
opaque disposePassManager (pm : PassManager ctx) : BaseIO Unit

@[extern "lean_llvm_run_pass_manager"]
opaque runPassManager (pm : PassManager ctx) (mod : Module ctx): BaseIO Unit

@[extern "lean_llvm_create_pass_manager_builder"]
opaque createPassManagerBuilder : BaseIO (PassManagerBuilder ctx)

@[extern "lean_llvm_dispose_pass_manager_builder"]
opaque disposePassManagerBuilder (pmb : PassManagerBuilder ctx) : BaseIO Unit

@[extern "lean_llvm_pass_manager_builder_set_opt_level"]
opaque PassManagerBuilder.setOptLevel (pmb : PassManagerBuilder ctx) (optLevel : unsigned) : BaseIO Unit

@[extern "lean_llvm_pass_manager_builder_populate_module_pass_manager"]
opaque PassManagerBuilder.populateModulePassManager (pmb : PassManagerBuilder ctx) (pm : PassManager ctx): BaseIO Unit

@[extern "lean_llvm_dispose_target_machine"]
opaque disposeTargetMachine (tm : TargetMachine ctx) : BaseIO Unit

@[extern "lean_llvm_dispose_module"]
opaque disposeModule (m : Module ctx) : BaseIO Unit

@[extern "lean_llvm_create_string_attribute"]
opaque createStringAttribute (key : String) (value : String) : BaseIO (Attribute ctx)

@[extern "lean_llvm_add_attribute_at_index"]
opaque addAttributeAtIndex (fn : Value ctx) (idx: AttributeIndex) (attr: Attribute ctx) : BaseIO Unit


-- https://github.com/llvm/llvm-project/blob/c3e073bcbdc523b0f758d44a89a6333e38bff863/llvm/include/llvm-c/Core.h#L198
structure Visibility where
  private mk :: val : UInt64

def Visibility.default   : Visibility := { val := 0 }
def Visibility.hidden    : Visibility := { val := 1 }
def Visibility.protected : Visibility := { val := 2 }

@[extern "lean_llvm_set_visibility"]
opaque setVisibility {ctx : Context} (value : Value ctx) (visibility : Visibility) : BaseIO Unit

-- https://github.com/llvm/llvm-project/blob/c3e073bcbdc523b0f758d44a89a6333e38bff863/llvm/include/llvm-c/Core.h#L210
structure DLLStorageClass where
  private mk :: val : UInt64

def DLLStorageClass.default : DLLStorageClass := { val := 0 }
def DLLStorageClass.import  : DLLStorageClass := { val := 1 }
def DLLStorageClass.export  : DLLStorageClass := { val := 2 }

@[extern "lean_llvm_set_dll_storage_class"]
opaque setDLLStorageClass {ctx : Context} (value : Value ctx) (dllStorageClass : DLLStorageClass) : BaseIO Unit

-- https://github.com/llvm/llvm-project/blob/c3e073bcbdc523b0f758d44a89a6333e38bff863/llvm/include/llvm-c/Core.h#L192
structure Linkage where
  private mk :: val : UInt64

/-- Externally visible function -/
def Linkage.external : Linkage := { val := 0 }
def Linkage.availableExternally : Linkage := { val := 1 }
/-- Keep one copy of function when linking (inline) -/
def Linkage.linkOnceAny : Linkage := { val := 2 }
/-- Same, but only replaced by something equivalent  -/
def Linkage.linkOnceODR : Linkage := { val := 3 }
/-- Obsolete -/
def Linkage.linkOnceODRAutoHide : Linkage := { val := 4 }
/-- Keep one copy of function when linking (weak) -/
def Linkage.weakAny : Linkage := { val := 5 }
/-- Same, but only replaced by something equivalent -/
def Linkage.weakODR : Linkage := { val := 6 }
/-- Special purpose, only applies to global arrays -/
def Linkage.appending : Linkage := { val := 7 }
/-- Rename collisions when linking (static functions) -/
def Linkage.internal : Linkage := { val := 8 }
/-- Like Internal, but omit from symbol table -/
def Linkage.private : Linkage := { val := 9 }
/-- Obsolete -/
def Linkage.dllImport : Linkage := { val := 10 }
/-- Obsolete -/
def Linkage.dllExport : Linkage := { val := 11 }
/-- ExternalWeak linkage description -/
def Linkage.externalWeak : Linkage := { val := 12 }
/-- Obsolete -/
def Linkage.ghost : Linkage := { val := 13 }
/-- Tentative definitions -/
def Linkage.common : Linkage := { val := 14 }
/-- Like Private, but linker removes. -/
def Linkage.linkerPrivate : Linkage := { val := 15 }
/-- Like LinkerPrivate, but is weak. -/
def Linkage.linkerPrivateWeak : Linkage := { val := 16 }

@[extern "lean_llvm_set_linkage"]
opaque setLinkage {ctx : Context} (value : Value ctx) (linkage : Linkage) : BaseIO Unit


def i1Type (ctx : LLVM.Context) : BaseIO (LLVM.LLVMType ctx) :=
  LLVM.intTypeInContext ctx 1

def i8Type (ctx : LLVM.Context) : BaseIO (LLVM.LLVMType ctx) :=
  LLVM.intTypeInContext ctx 8

def i16Type (ctx : LLVM.Context) : BaseIO (LLVM.LLVMType ctx) :=
  LLVM.intTypeInContext ctx 16

def i32Type (ctx : LLVM.Context) : BaseIO (LLVM.LLVMType ctx) :=
  LLVM.intTypeInContext ctx 32

def i64Type (ctx : LLVM.Context) : BaseIO (LLVM.LLVMType ctx) :=
  LLVM.intTypeInContext ctx 64

def voidPtrType (ctx : LLVM.Context) : BaseIO (LLVM.LLVMType ctx) :=
  do LLVM.pointerType (← LLVM.intTypeInContext ctx 8)

def i8PtrType (ctx : LLVM.Context) : BaseIO (LLVM.LLVMType ctx) :=
  voidPtrType ctx

def constTrue (ctx : Context) : BaseIO (Value ctx) :=
  do constInt (← i1Type ctx) 1 (signExtend := false)

def constFalse (ctx : Context) : BaseIO (Value ctx) :=
  do constInt (← i1Type ctx) 0 (signExtend := false)

def constInt' (ctx : Context) (width : UInt64) (value : UInt64) (signExtend : Bool := false) : BaseIO (Value ctx) :=
 do constInt (← LLVM.intTypeInContext ctx width) value signExtend

def constInt1 (ctx : Context) (value : UInt64) (signExtend : Bool := false) : BaseIO (Value ctx) :=
  constInt' ctx 1 value signExtend

def constInt8 (ctx : Context) (value : UInt64) (signExtend : Bool := false) : BaseIO (Value ctx) :=
  constInt' ctx 8 value signExtend

def constInt32 (ctx : Context) (value : UInt64) (signExtend : Bool := false) : BaseIO (Value ctx) :=
  constInt' ctx 32 value signExtend

def constInt64 (ctx : Context) (value : UInt64) (signExtend : Bool := false) : BaseIO (Value ctx) :=
  constInt' ctx 64 value signExtend

def constIntUnsigned (ctx : Context) (value : UInt64) (signExtend : Bool := false) : BaseIO (Value ctx) :=
  constInt' ctx 64 value signExtend
end LLVM
