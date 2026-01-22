// Lean compiler output
// Module: Lean.Compiler.IR.EmitC
// Imports: public import Lean.Compiler.NameMangling public import Lean.Compiler.IR.EmitUtil public import Lean.Compiler.IR.NormIds public import Lean.Compiler.IR.SimpCase public import Lean.Compiler.IR.Boxing public import Lean.Compiler.IR.StructRC public import Lean.Compiler.ModPkgExt
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__0;
extern lean_object* l_Lean_IR_instInhabitedArg_default;
uint8_t l_Lean_IR_IRType_isScalarOrStruct(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__25;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitInitFn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructBox___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__9;
lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__0;
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitCtor___closed__4;
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__10;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__7;
static lean_object* l_Lean_IR_EmitC_emitBlock___closed__0;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_optionLike_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBoxFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isVoid(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__22;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__34;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__24;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__45;
static lean_object* l_Lean_IR_EmitC_emitReuse___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnboxFn___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqJoinPointId_beq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_structBoxFnPrefix;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6;
lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreadArgs_spec__0(uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_emitStructReshapeFn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_collectStructTypes(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructBox___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLn___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_emitC___closed__0;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__4;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__17;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBoxFn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_argToCString___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__47;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__16;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__7;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__23;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_structUnboxFnPrefix;
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__4;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__19;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__21;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__4;
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_IR_instBEqIRTypeApprox___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__8;
static lean_object* l_Lean_IR_EmitC_emitMarkPersistent___closed__0;
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__8;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCName___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructBoxFn___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__8;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_optionLikePath___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_EmitC_needsRC_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitCtor___closed__2;
lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__44;
uint8_t l_Lean_IR_instBEqIRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams(lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3;
static lean_object* l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitTag___closed__2;
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__5;
static lean_object* l_Lean_IR_EmitC_emitSpreadArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitStructDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__0;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4;
uint8_t l_Lean_IR_IRType_isErased(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReset___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__4;
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_structBoxFnPrefix___closed__0;
static lean_object* l_Lean_IR_EmitC_emitSpreadArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_IR_EmitC_emitApp___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_export_name_for(lean_object*, lean_object*);
uint8_t l_Lean_isClosedTermName(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__12;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitTag___closed__1;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__1;
static lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_symbol_stem(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_structUnboxFnPrefix___closed__0;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__15;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_optionLikePath(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_argToCString___closed__0;
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCName(lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__3;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__5;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___closed__0;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__20;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_structIncFnPrefix___closed__0;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreadArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__7;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__19;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitStructDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__32;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_IR_EmitC_toCName___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__15;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object*);
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_structType(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__2;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__9;
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars(lean_object*, uint8_t, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0;
lean_object* l_Lean_IR_ensureHasDefault(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___closed__5;
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_compatibleReshape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__38;
static lean_object* l_Lean_IR_EmitC_emitIf___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIncOfType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructUnboxFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullAppArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_lookupStruct___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSet___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__53;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn___lam__0___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSpreadValue___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__26;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructBox___closed__4;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__2;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__18;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_IR_EmitC_emitFnDecls_spec__2(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_hasMainFn___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__4;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUProj___closed__2;
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__0;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructBox___closed__2;
static lean_object* l_Lean_IR_EmitC_leanMainFn___closed__0;
static lean_object* l_Lean_IR_EmitC_emitStructBox___closed__6;
uint8_t l_Lean_IR_usesModuleFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam_default;
uint8_t l_Lean_IR_IRType_compatibleWith(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__5;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_IR_EmitC_lookupStruct___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIOUnitBuiltinInitFn(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__9;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitIncOfType___closed__4;
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__5;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__1;
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__6;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__3;
extern lean_object* l_Lean_closureMaxArgs;
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__7;
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitIsShared___redArg___closed__0;
lean_object* l_Lean_IR_IRType_hashApprox___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSetTag___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreads(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__0;
static lean_object* l_Lean_IR_EmitC_emitTailCall___closed__1;
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_optionLike_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__51;
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_getJPParams___closed__0;
static lean_object* l_Lean_IR_EmitC_emitTailCall___closed__2;
uint8_t l_Lean_isExternC(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__3;
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_emitMainFn_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__4;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__50;
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__6;
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__5;
lean_object* l_Lean_IR_Decl_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_compatibleReshape___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitSpreadArg_match__10_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_argToCString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReuse___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_needsRC(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__7;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__2;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__2;
static lean_object* l_Lean_IR_EmitC_emitCase___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__0;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitIncOfType___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullAppArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__37;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_StructRC_visitDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__30;
static lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDel___redArg___closed__0;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0;
static lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__5;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__12;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__23;
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__0;
static lean_object* l_Lean_IR_EmitC_emitIncOfType___closed__2;
static lean_object* l_Lean_IR_EmitC_emitCtor___closed__1;
static lean_object* l_Lean_IR_EmitC_emitStructBox___closed__0;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__8;
static lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__6;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_IR_EmitC_toStringArgs_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__46;
static lean_object* l_Lean_IR_EmitC_emitCase___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitCtor___closed__0;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitInitFn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitJmp___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_hasMainFn___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitApp___closed__1;
static lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_EmitC_needsRC_spec__0(lean_object*, size_t, size_t);
static lean_object* l_Lean_IR_EmitC_emitTailCall___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___lam__0___boxed(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitJmp___closed__1;
static lean_object* l_Lean_IR_EmitC_toCInitName___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__36;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__0;
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__6;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__0;
static lean_object* l_Lean_IR_EmitC_getDecl___closed__0;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__17;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecOfType(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__4;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitIncOfType___closed__1;
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__4;
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__24;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__9;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitTailCall___closed__3;
lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_IR_IRType_hashApprox(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__42;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBlock(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitProj___closed__0;
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructBox___closed__3;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_structReshapeFnPrefix;
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCInitName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBlock___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__41;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructDeclsFor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitPath___closed__0;
static lean_object* l_Lean_IR_EmitC_emitStructBoxFn___closed__2;
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__2;
static lean_object* l_Lean_IR_EmitC_emitUProj___closed__0;
lean_object* l_Lean_getBuiltinInitFnNameFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReshapeFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullAppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__39;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__33;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadArgs(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__2;
static lean_object* l_Lean_IR_EmitC_structDecFnPrefix___closed__0;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__8;
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__5;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0;
static lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lean_IR_EmitC_emitOffset___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_quoteString___closed__0;
static lean_object* l_Lean_IR_EmitC_emitApp___closed__4;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__55;
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUnionSwitch___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitIf___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitIncOfType___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitSpreadArg_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_leanMainFn;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_main___closed__0;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__7;
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__31;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__11;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBoxFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLit___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__21;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_structIncFnPrefix;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__10;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__28;
lean_object* l_Lean_IR_getDecls(lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0___closed__0;
static lean_object* l_Lean_IR_EmitC_toCType___closed__5;
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__6;
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___closed__0;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__13;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_isTailCallTo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_IR_EmitC_emitFnDecls_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__0;
static lean_object* l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1;
uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___lam__0(lean_object*);
lean_object* l_Lean_IR_getUnboxOpName(lean_object*);
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0;
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___closed__5;
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0___closed__0;
lean_object* l_Lean_IR_Alt_body(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__40;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__54;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUProj___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___closed__0;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__16;
lean_object* l_Lean_IR_mkVarJPMaps(lean_object*);
static lean_object* l_Lean_IR_EmitC_optionLikePath___closed__1;
static lean_object* l_Lean_IR_EmitC_emitJmp___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReset___closed__2;
static lean_object* l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__22;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnboxFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_lookupStruct(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__2;
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__48;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__10;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFns_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitIf___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitSpreadArg_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__13;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_main___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_main(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__1;
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___closed__0;
static lean_object* l_Lean_IR_EmitC_emitApp___closed__2;
lean_object* l_Lean_Environment_imports(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructDecls(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__52;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__1;
lean_object* l_Lean_IR_declToString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5;
uint64_t l_Lean_IR_instHashableJoinPointId_hash(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
static lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__27;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFns(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_lookupStruct___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___closed__7;
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__2;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__49;
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReshapeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPath___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedStructTypeInfo_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReset___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__4;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__35;
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__14;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2;
static lean_object* l_Lean_IR_EmitC_emitUProj___closed__1;
static lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__2;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__14;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructDecls___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_structType___closed__0;
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__5;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1;
static lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__5;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructDefn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIOUnitInitFn(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitExternCall___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitOffset___redArg___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
static lean_object* l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0;
uint64_t l_Lean_IR_instHashableVarId_hash(lean_object*);
lean_object* l_Lean_IR_collectUsedDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitTag___closed__0;
static lean_object* l_Lean_IR_EmitC_getDecl___closed__1;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__1;
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__1;
static lean_object* l_Lean_IR_EmitC_main___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__43;
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__5;
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__3;
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJPs(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReset___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_structDecFnPrefix;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecOfType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructBoxFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_needsRC___boxed(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__0;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreads___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__4;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIncOfType(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__5;
static lean_object* l_Lean_IR_EmitC_emitStructDefn___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitSpreadArg_match__10_splitter___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitJPs___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModInitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModulePackageByIdx_x3f(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructBoxFn___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_emitC(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___closed__3;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitCtor___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__29;
static lean_object* l_Lean_IR_emitC___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__18;
static lean_object* l_Lean_IR_EmitC_declareVar___closed__0;
static lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___closed__2;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__20;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_optionLikePath___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__3;
static lean_object* l_Lean_IR_EmitC_emitSpreadValue___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_EmitC_leanMainFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_lean_main", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_leanMainFn() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_leanMainFn___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getModName(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModInitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = l_Lean_PersistentEnvExtension_getState___redArg(x_8, x_5, x_3, x_7, x_9);
lean_dec(x_7);
x_11 = l_Lean_mkModuleInitializationFunctionName(x_4, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_IR_EmitC_getDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown declaration '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = 0;
lean_inc(x_1);
x_6 = l_Lean_IR_findEnvDecl(x_4, x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_IR_EmitC_getDecl___closed__0;
x_8 = 1;
x_9 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_getDecl___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec_ref(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_3);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emit(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLn___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
x_6 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_7 = lean_box(0);
x_8 = lean_string_append(x_5, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_9 = lean_box(0);
x_10 = lean_string_append(x_7, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLn(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_8 = lean_box(0);
x_9 = lean_string_append(x_6, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLns___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__0), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_map), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitLns___redArg___closed__0;
x_2 = l_Lean_IR_EmitC_emitLns___redArg___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitLns___redArg___closed__6;
x_2 = l_Lean_IR_EmitC_emitLns___redArg___closed__2;
x_3 = l_Lean_IR_EmitC_emitLns___redArg___closed__1;
x_4 = l_Lean_IR_EmitC_emitLns___redArg___closed__5;
x_5 = l_Lean_IR_EmitC_emitLns___redArg___closed__4;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_bind), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitLns___redArg___closed__8;
x_2 = l_Lean_IR_EmitC_emitLns___redArg___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_EmitC_emitLns___redArg___closed__9;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitLns___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_IR_EmitC_emitLns___redArg___closed__10;
x_7 = l_List_forM___redArg(x_6, x_2, x_5);
x_8 = lean_apply_2(x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLns___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_argToCString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x_", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_argToCString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box(0)", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_argToCString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_IR_EmitC_argToCString___closed__0;
x_4 = l_Nat_reprFast(x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_argToCString___closed__1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_IR_EmitC_argToCString(x_1);
x_4 = lean_box(0);
x_5 = lean_string_append(x_2, x_3);
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArg___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_lookupStruct___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instBEqIRTypeApprox___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_lookupStruct___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_IRType_hashApprox___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_lookupStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 6);
x_5 = l_Lean_IR_EmitC_lookupStruct___closed__0;
x_6 = l_Lean_IR_EmitC_lookupStruct___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(x_5, x_6, x_7, x_4, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_lookupStruct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_lookupStruct(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("struct l_s", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_structType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_EmitC_structType___closed__0;
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(163u);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__1;
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__3;
x_5 = lean_panic_fn(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = 1;
x_10 = l_Lean_IR_IRType_compatibleWith(x_6, x_2, x_9);
if (x_10 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_IR_IRType_hashApprox(x_3);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_4, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg(x_1, x_3, x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("double", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uint8_t", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uint16_t", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uint32_t", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uint64_t", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("size_t", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("float", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_object*", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_EmitC_toCType___closed__0;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_EmitC_toCType___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_EmitC_toCType___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_IR_EmitC_toCType___closed__3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
case 4:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_IR_EmitC_toCType___closed__4;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_IR_EmitC_toCType___closed__5;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
case 9:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_IR_EmitC_toCType___closed__6;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
case 10:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_19, x_18, x_1);
lean_dec_ref(x_1);
x_21 = l_Lean_IR_EmitC_structType(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
case 11:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_2, 6);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_24, x_23, x_1);
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_1, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_dec(x_28);
x_29 = l_Lean_IR_EmitC_structType(x_25);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_29);
return x_1;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = l_Lean_IR_EmitC_structType(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
default: 
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = l_Lean_IR_EmitC_toCType___closed__7;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCType(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid export name '", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0;
x_4 = 1;
x_5 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = l_Lean_IR_EmitC_getDecl___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_throwInvalidExportName(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_EmitC_toCName___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1);
lean_inc_ref(x_4);
x_5 = lean_get_export_name_for(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_IR_EmitC_toCName___closed__1;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_get_symbol_stem(x_4, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_10 = l_Lean_IR_EmitC_leanMainFn___closed__0;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec_ref(x_5);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_12);
x_16 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_1, x_3);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCName(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
x_9 = lean_string_append(x_7, x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCInitName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_init_", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCInitName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1);
lean_inc_ref(x_4);
x_5 = lean_get_export_name_for(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_IR_EmitC_toCInitName___closed__0;
x_7 = lean_get_symbol_stem(x_4, x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec_ref(x_5);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_IR_EmitC_toCInitName___closed__0;
x_14 = lean_string_append(x_13, x_12);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_10);
x_16 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_1, x_3);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_10);
x_17 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCInitName(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
x_9 = lean_string_append(x_7, x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSpreadArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSpreadArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_22; lean_object* x_23; 
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_30, x_32);
if (x_33 == 0)
{
x_22 = x_4;
x_23 = x_5;
goto block_28;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_eq(x_31, x_32);
if (x_34 == 0)
{
x_22 = x_4;
x_23 = x_5;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_29);
lean_dec_ref(x_1);
x_35 = lean_array_get_size(x_29);
x_36 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg(x_35, x_29, x_2, x_32, x_3, x_4, x_5);
lean_dec_ref(x_29);
return x_36;
}
}
}
else
{
x_22 = x_4;
x_23 = x_5;
goto block_28;
}
block_10:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
block_21:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_IR_EmitC_toCType(x_1, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_19 = lean_string_append(x_16, x_18);
x_20 = lean_string_append(x_19, x_17);
lean_dec(x_17);
x_6 = x_20;
goto block_10;
}
else
{
lean_dec(x_2);
x_6 = x_16;
goto block_10;
}
}
block_28:
{
if (lean_obj_tag(x_1) == 13)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_box(x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
else
{
if (x_3 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_27 = lean_string_append(x_23, x_26);
x_11 = x_22;
x_12 = x_27;
goto block_21;
}
else
{
x_11 = x_22;
x_12 = x_23;
goto block_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_4, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_box(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget_borrowed(x_2, x_4);
if (lean_obj_tag(x_17) == 6)
{
x_8 = x_5;
x_9 = x_7;
goto block_13;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
x_18 = x_3;
goto block_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0;
lean_inc(x_24);
x_26 = lean_string_append(x_24, x_25);
lean_inc(x_4);
x_27 = l_Nat_reprFast(x_4);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_18 = x_29;
goto block_23;
}
}
block_23:
{
lean_object* x_19; 
lean_inc(x_17);
x_19 = l_Lean_IR_EmitC_emitSpreadArg(x_17, x_18, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_unbox(x_20);
lean_dec(x_20);
x_8 = x_22;
x_9 = x_21;
goto block_13;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitSpreadArg(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitSpreadArg_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_2(x_3, x_1, lean_box(0));
return x_10;
}
else
{
uint8_t x_11; 
lean_inc(x_7);
lean_inc_ref(x_5);
lean_inc(x_4);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = lean_nat_dec_eq(x_7, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
lean_ctor_set(x_1, 2, x_8);
x_17 = lean_apply_2(x_3, x_1, lean_box(0));
return x_17;
}
else
{
lean_object* x_18; 
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_3);
x_18 = lean_apply_2(x_2, x_4, x_5);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = lean_nat_dec_eq(x_7, x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_7);
x_21 = lean_apply_2(x_3, x_20, lean_box(0));
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_3);
x_22 = lean_apply_2(x_2, x_4, x_5);
return x_22;
}
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_apply_2(x_3, x_1, lean_box(0));
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitSpreadArg_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_apply_2(x_4, x_2, lean_box(0));
return x_11;
}
else
{
uint8_t x_12; 
lean_inc(x_8);
lean_inc_ref(x_6);
lean_inc(x_5);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_2, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = lean_nat_dec_eq(x_8, x_9);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
lean_ctor_set(x_2, 2, x_9);
x_18 = lean_apply_2(x_4, x_2, lean_box(0));
return x_18;
}
else
{
lean_object* x_19; 
lean_free_object(x_2);
lean_dec(x_8);
lean_dec(x_4);
x_19 = lean_apply_2(x_3, x_5, x_6);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = lean_nat_dec_eq(x_8, x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_8);
x_22 = lean_apply_2(x_4, x_21, lean_box(0));
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_4);
x_23 = lean_apply_2(x_3, x_5, x_6);
return x_23;
}
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_3);
x_24 = lean_apply_2(x_4, x_2, lean_box(0));
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitSpreadArg_match__10_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitSpreadArg_match__10_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreadArgs_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
if (x_1 == 0)
{
lean_object* x_23; 
lean_dec(x_12);
x_23 = lean_box(0);
x_14 = x_23;
goto block_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_IR_EmitC_argToCString___closed__0;
x_25 = l_Nat_reprFast(x_12);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_14 = x_27;
goto block_22;
}
block_22:
{
lean_object* x_15; 
x_15 = l_Lean_IR_EmitC_emitSpreadArg(x_13, x_14, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_20 = lean_unbox(x_16);
lean_dec(x_16);
x_4 = x_19;
x_5 = x_20;
x_7 = x_17;
goto _start;
}
else
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreadArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreadArgs_spec__0(x_8, x_2, x_9, x_10, x_11, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadArgs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = 1;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreadArgs_spec__0(x_2, x_1, x_6, x_7, x_5, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_IR_EmitC_emitSpreadArgs(x_1, x_5, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".i", 2, 2);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSpreadValue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_14; uint8_t x_30; 
x_30 = lean_nat_dec_lt(x_4, x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_31 = lean_box(x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_array_fget_borrowed(x_2, x_4);
switch (lean_obj_tag(x_33)) {
case 6:
{
x_8 = x_5;
x_9 = x_7;
goto block_13;
}
case 13:
{
x_8 = x_5;
x_9 = x_7;
goto block_13;
}
default: 
{
uint8_t x_34; 
x_34 = 0;
if (x_5 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_36 = lean_box(0);
x_37 = lean_string_append(x_7, x_35);
lean_inc_ref(x_3);
lean_inc(x_4);
x_38 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0(x_4, x_3, x_33, x_34, x_5, x_36, x_6, x_37);
x_14 = x_38;
goto block_29;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
lean_inc_ref(x_3);
lean_inc(x_4);
x_40 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0(x_4, x_3, x_33, x_34, x_5, x_39, x_6, x_7);
x_14 = x_40;
goto block_29;
}
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
block_29:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec_ref(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec_ref(x_15);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
x_8 = x_24;
x_9 = x_22;
goto block_13;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSpreadValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_11, x_13);
if (x_14 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_12, x_13);
if (x_15 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_get_size(x_10);
x_17 = l_Lean_IR_EmitC_emitSpreadValue___closed__0;
x_18 = lean_string_append(x_4, x_17);
x_19 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg(x_16, x_10, x_2, x_13, x_15, x_3, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_24 = lean_string_append(x_21, x_23);
x_25 = lean_box(0);
lean_ctor_set(x_19, 1, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
else
{
x_5 = x_4;
goto block_9;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_string_append(x_5, x_2);
lean_dec_ref(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_reprFast(x_1);
x_12 = lean_string_append(x_10, x_11);
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0;
x_16 = lean_string_append(x_2, x_15);
x_17 = lean_string_append(x_16, x_11);
lean_dec_ref(x_11);
x_18 = l_Lean_IR_EmitC_emitSpreadValue(x_3, x_17, x_7, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(x_4);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(x_4);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_4);
x_10 = lean_unbox(x_5);
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreadValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitSpreadValue(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = (", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(";", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_2, x_4);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 10)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 2);
x_20 = lean_ctor_get(x_17, 3);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_19, x_21);
if (x_22 == 0)
{
lean_dec(x_18);
lean_dec_ref(x_17);
x_8 = x_1;
x_9 = x_7;
goto block_13;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_20, x_21);
if (x_23 == 0)
{
lean_dec(x_18);
lean_dec_ref(x_17);
x_8 = x_1;
x_9 = x_7;
goto block_13;
}
else
{
lean_object* x_24; 
lean_inc_ref(x_17);
x_24 = l_Lean_IR_EmitC_toCType(x_17, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_argToCString___closed__0;
x_31 = l_Nat_reprFast(x_18);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = lean_string_append(x_29, x_32);
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__0;
x_35 = lean_string_append(x_33, x_34);
lean_inc_ref(x_17);
x_36 = l_Lean_IR_EmitC_toCType(x_17, x_6, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lean_IR_EmitC_emitSpreadValue(x_17, x_32, x_6, x_41);
lean_dec_ref(x_17);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_47 = lean_string_append(x_45, x_46);
x_8 = x_1;
x_9 = x_47;
goto block_13;
}
else
{
return x_42;
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_32);
lean_dec_ref(x_17);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
return x_36;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_18);
lean_dec_ref(x_17);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
return x_24;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_24, 0);
x_54 = lean_ctor_get(x_24, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_24);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
x_8 = x_1;
x_9 = x_7;
goto block_13;
}
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreads(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_array_size(x_1);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0(x_4, x_1, x_5, x_6, x_4, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSpreads___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitSpreads(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullAppArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; 
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_19, x_21);
if (x_22 == 0)
{
x_12 = x_5;
goto block_17;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_20, x_21);
if (x_23 == 0)
{
x_12 = x_5;
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_array_get_size(x_18);
x_25 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___redArg(x_24, x_18, x_2, x_21, x_3, x_4, x_5);
return x_25;
}
}
}
else
{
x_12 = x_5;
goto block_17;
}
block_11:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_string_append(x_6, x_2);
lean_dec_ref(x_2);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
block_17:
{
if (lean_obj_tag(x_1) == 13)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_2);
x_13 = lean_box(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
if (x_3 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_16 = lean_string_append(x_12, x_15);
x_6 = x_16;
goto block_11;
}
else
{
x_6 = x_12;
goto block_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_4, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = lean_box(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_array_fget_borrowed(x_2, x_4);
switch (lean_obj_tag(x_17)) {
case 6:
{
x_8 = x_5;
x_9 = x_7;
goto block_13;
}
case 13:
{
x_8 = x_5;
x_9 = x_7;
goto block_13;
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
lean_inc_ref(x_3);
x_19 = lean_string_append(x_3, x_18);
lean_inc(x_4);
x_20 = l_Nat_reprFast(x_4);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = l_Lean_IR_EmitC_emitFullAppArg(x_17, x_21, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_unbox(x_23);
lean_dec(x_23);
x_8 = x_25;
x_9 = x_24;
goto block_13;
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
return x_22;
}
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullAppArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitFullAppArg(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArg_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_IR_EmitC_argToCString___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_box(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___lam__0(x_6, x_7, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_15; uint8_t x_31; 
x_31 = lean_nat_dec_lt(x_5, x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_32 = lean_box(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_2);
x_34 = lean_array_get_borrowed(x_2, x_3, x_5);
x_35 = lean_ctor_get(x_34, 1);
if (lean_obj_tag(x_35) == 13)
{
x_9 = x_6;
x_10 = x_8;
goto block_14;
}
else
{
lean_object* x_36; 
x_36 = lean_array_fget_borrowed(x_4, x_5);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
x_38 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_37);
x_39 = l_Nat_reprFast(x_37);
x_40 = lean_string_append(x_38, x_39);
lean_dec_ref(x_39);
x_41 = l_Lean_IR_EmitC_emitFullAppArg(x_35, x_40, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_unbox(x_42);
lean_dec(x_42);
x_9 = x_44;
x_10 = x_43;
goto block_14;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_2);
return x_41;
}
}
else
{
uint8_t x_45; 
x_45 = 0;
if (x_6 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_47 = lean_box(0);
x_48 = lean_string_append(x_8, x_46);
x_49 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___lam__0(x_45, x_6, x_47, x_7, x_48);
x_15 = x_49;
goto block_30;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___lam__0(x_45, x_6, x_50, x_7, x_8);
x_15 = x_51;
goto block_30;
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
x_6 = x_9;
x_8 = x_10;
goto _start;
}
block_30:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec_ref(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec_ref(x_15);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec_ref(x_16);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
x_9 = x_25;
x_10 = x_23;
goto block_14;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = l_Lean_IR_instInhabitedParam_default;
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 1;
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg(x_6, x_5, x_1, x_2, x_7, x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitFullAppArgs(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_8);
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitFullAppArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = l_Lean_IR_IRType_isVoid(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_4, x_11);
x_5 = x_14;
goto block_9;
}
else
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = l_Lean_IR_IRType_isErased(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_4, x_11);
x_5 = x_14;
goto block_9;
}
else
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_object**", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_EXPORT ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extern ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_83; 
x_36 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_36);
x_54 = l_Lean_IR_Decl_params(x_1);
x_83 = l_Array_isEmpty___redArg(x_54);
if (x_83 == 0)
{
if (x_3 == 0)
{
goto block_82;
}
else
{
if (x_83 == 0)
{
x_55 = x_4;
x_56 = x_5;
goto block_79;
}
else
{
goto block_82;
}
}
}
else
{
if (x_3 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = l_Lean_IR_Decl_name(x_1);
lean_inc_ref(x_36);
x_85 = l_Lean_isClosedTermName(x_36, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
x_87 = lean_string_append(x_5, x_86);
x_55 = x_4;
x_56 = x_87;
goto block_79;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_IR_EmitC_emitFnDeclAux___closed__4;
x_89 = lean_string_append(x_5, x_88);
x_55 = x_4;
x_56 = x_89;
goto block_79;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Lean_IR_EmitC_emitFnDeclAux___closed__5;
x_91 = lean_string_append(x_5, x_90);
x_55 = x_4;
x_56 = x_91;
goto block_79;
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_10 = lean_box(0);
x_11 = lean_string_append(x_8, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_6 = x_16;
goto block_13;
}
block_26:
{
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_IR_EmitC_emitSpreadArgs(x_19, x_21, x_20, x_18);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_14 = x_23;
goto block_17;
}
else
{
return x_22;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_20);
lean_dec_ref(x_19);
x_24 = l_Lean_IR_EmitC_emitFnDeclAux___closed__0;
x_25 = lean_string_append(x_18, x_24);
x_14 = x_25;
goto block_17;
}
}
block_35:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_closureMaxArgs;
x_32 = lean_array_get_size(x_30);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_dec(x_28);
x_18 = x_27;
x_19 = x_30;
x_20 = x_29;
x_21 = x_33;
goto block_26;
}
else
{
uint8_t x_34; 
x_34 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_28);
lean_dec(x_28);
x_18 = x_27;
x_19 = x_30;
x_20 = x_29;
x_21 = x_34;
goto block_26;
}
}
block_53:
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_41);
x_42 = l_Lean_isExternC(x_36, x_41);
if (x_42 == 0)
{
x_27 = x_37;
x_28 = x_41;
x_29 = x_39;
x_30 = x_40;
goto block_35;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_array_get_size(x_40);
x_44 = lean_mk_empty_array_with_capacity(x_38);
x_45 = lean_nat_dec_lt(x_38, x_43);
if (x_45 == 0)
{
lean_dec_ref(x_40);
x_27 = x_37;
x_28 = x_41;
x_29 = x_39;
x_30 = x_44;
goto block_35;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
if (x_45 == 0)
{
lean_dec_ref(x_40);
x_27 = x_37;
x_28 = x_41;
x_29 = x_39;
x_30 = x_44;
goto block_35;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_43);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0(x_40, x_47, x_48, x_44);
lean_dec_ref(x_40);
x_27 = x_37;
x_28 = x_41;
x_29 = x_39;
x_30 = x_49;
goto block_35;
}
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_43);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0(x_40, x_50, x_51, x_44);
lean_dec_ref(x_40);
x_27 = x_37;
x_28 = x_41;
x_29 = x_39;
x_30 = x_52;
goto block_35;
}
}
}
}
block_79:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_57 = l_Lean_IR_Decl_resultType(x_1);
x_58 = l_Lean_IR_EmitC_toCType(x_57, x_55, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_62 = lean_string_append(x_59, x_61);
x_63 = lean_string_append(x_62, x_2);
x_64 = lean_string_append(x_60, x_63);
lean_dec_ref(x_63);
x_65 = l_Array_isEmpty___redArg(x_54);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_67 = lean_string_append(x_64, x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_array_get_size(x_54);
x_70 = l_Lean_IR_EmitC_emitFnDeclAux___closed__2;
x_71 = lean_nat_dec_lt(x_68, x_69);
if (x_71 == 0)
{
lean_dec_ref(x_54);
x_37 = x_67;
x_38 = x_68;
x_39 = x_55;
x_40 = x_70;
goto block_53;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_69, x_69);
if (x_72 == 0)
{
if (x_71 == 0)
{
lean_dec_ref(x_54);
x_37 = x_67;
x_38 = x_68;
x_39 = x_55;
x_40 = x_70;
goto block_53;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_69);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_54, x_73, x_74, x_70);
lean_dec_ref(x_54);
x_37 = x_67;
x_38 = x_68;
x_39 = x_55;
x_40 = x_75;
goto block_53;
}
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_69);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_54, x_76, x_77, x_70);
lean_dec_ref(x_54);
x_37 = x_67;
x_38 = x_68;
x_39 = x_55;
x_40 = x_78;
goto block_53;
}
}
}
else
{
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_36);
x_6 = x_64;
goto block_13;
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
x_81 = lean_string_append(x_5, x_80);
x_55 = x_4;
x_56 = x_81;
goto block_79;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_Decl_name(x_1);
lean_inc_ref(x_3);
x_6 = l_Lean_IR_EmitC_toCName(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec_ref(x_3);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_IR_EmitC_emitFnDecl(x_1, x_5, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_Decl_name(x_1);
lean_inc_ref(x_5);
x_7 = l_Lean_isExternC(x_5, x_6);
x_8 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitExternDeclAux(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_Decl_name(x_3);
x_6 = l_Lean_NameSet_insert(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_IR_Decl_name(x_4);
x_7 = l_Lean_NameSet_insert(x_2, x_6);
lean_inc_ref(x_1);
x_8 = l_Lean_IR_collectUsedDecls(x_1, x_4, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_IR_EmitC_emitFnDecls_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_IR_EmitC_emitFnDecls_spec__2(x_1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_IR_EmitC_emitFnDecls_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_IR_EmitC_emitFnDecls_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
lean_inc(x_8);
x_14 = l_Lean_IR_EmitC_getDecl(x_8, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__1;
x_18 = l_Lean_IR_Decl_name(x_15);
lean_inc_ref(x_1);
x_19 = l_Lean_getExternNameFor(x_1, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = l_Lean_NameSet_contains(x_2, x_8);
lean_dec(x_8);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
lean_inc_ref(x_4);
x_22 = l_Lean_IR_EmitC_emitFnDecl(x_15, x_21, x_4, x_16);
lean_dec(x_15);
x_10 = x_22;
goto block_13;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
lean_inc_ref(x_4);
x_24 = l_Lean_IR_EmitC_emitFnDecl(x_15, x_23, x_4, x_16);
lean_dec(x_15);
x_10 = x_24;
goto block_13;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec_ref(x_19);
lean_inc_ref(x_4);
x_26 = l_Lean_IR_EmitC_emitExternDeclAux(x_15, x_25, x_4, x_16);
lean_dec(x_25);
lean_dec(x_15);
x_10 = x_26;
goto block_13;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
block_13:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_3 = x_9;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_inc_ref(x_3);
x_4 = l_Lean_IR_getDecls(x_3);
x_5 = l_Lean_NameSet_empty;
x_6 = l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0(x_5, x_4);
lean_inc_ref(x_3);
x_7 = l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__1(x_3, x_5, x_4);
x_8 = lean_box(0);
x_9 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_IR_EmitC_emitFnDecls_spec__2(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3(x_3, x_6, x_9, x_1, x_2);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_name_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_emitMainFn_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedConstantInfo_default;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_append(x_2, x_5);
x_8 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  lean_dec_ref(res);", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  return ret;", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("} else {", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  lean_io_result_show_error(res);", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  return 1;", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_finalize_task_manager();", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  int ret = ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt32", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__8;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0;", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_unbox_uint32(lean_io_result_get_value(res));", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__14;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_5 = l_Lean_IR_EmitC_emitMainFn___closed__12;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_set_panic_messages(false);", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("res = ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(1 /* builtin */);", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_set_panic_messages(true);", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_io_mark_end_initialization();", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (lean_io_result_is_ok(res)) {", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_dec_ref(res);", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_init_task_manager();", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__24;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__25;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__26;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("res = _lean_main();", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("in = lean_box(0);", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("int i = argc;", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("while (i > 1) {", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" lean_object* n;", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" i--;", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);", 99, 99);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" in = n;", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__36;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__35;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__37;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__34;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__38;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__39;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__32;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__40;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__31;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__41;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__42;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("res = _lean_main(in);", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  #if defined(WIN32) || defined(_WIN32)\n  #include <windows.h>\n  #endif\n\n  int main(int argc, char ** argv) {\n  #if defined(WIN32) || defined(_WIN32)\n  SetErrorMode(SEM_FAILCRITICALERRORS);\n  SetConsoleOutputCP(CP_UTF8);\n  #endif\n  lean_object* in; lean_object* res;", 267, 267);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("argv = lean_setup_args(argc, argv);", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_initialize_runtime_module();", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_initialize();", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid main function, incorrect arity when generating code", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__50;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("char ** lean_setup_args(int argc, char ** argv);", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__53() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("void lean_initialize_runtime_module();", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("void lean_initialize();", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__55() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("function declaration expected", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_75; 
x_59 = l_Lean_IR_EmitC_toCName___closed__1;
lean_inc_ref(x_1);
x_75 = l_Lean_IR_EmitC_getDecl(x_59, x_1, x_2);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_141; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_76, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_76);
x_158 = lean_array_get_size(x_79);
x_159 = lean_unsigned_to_nat(2u);
x_160 = lean_nat_dec_eq(x_158, x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_dec_eq(x_158, x_161);
x_141 = x_162;
goto block_157;
}
else
{
x_141 = x_160;
goto block_157;
}
block_122:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
x_85 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_86 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_IR_EmitC_emitMainFn___closed__16;
x_89 = lean_string_append(x_82, x_88);
x_90 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_box(0);
x_93 = lean_box(0);
lean_inc_ref(x_83);
x_94 = l_Lean_PersistentEnvExtension_getState___redArg(x_92, x_85, x_83, x_87, x_93);
lean_dec(x_87);
lean_inc(x_84);
x_95 = l_Lean_mkModuleInitializationFunctionName(x_84, x_94);
lean_dec(x_94);
x_96 = l_Lean_IR_EmitC_emitMainFn___closed__17;
x_97 = lean_string_append(x_96, x_95);
lean_dec_ref(x_95);
x_98 = l_Lean_IR_EmitC_emitMainFn___closed__18;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_string_append(x_91, x_99);
lean_dec_ref(x_99);
x_101 = lean_string_append(x_100, x_90);
x_102 = l_Lean_IR_EmitC_emitMainFn___closed__19;
x_103 = lean_string_append(x_101, x_102);
x_104 = lean_string_append(x_103, x_90);
x_105 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_106 = lean_box(0);
x_107 = l_Lean_IR_EmitC_emitMainFn___closed__27;
x_108 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_107, x_104);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_array_get_size(x_79);
lean_dec_ref(x_79);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_nat_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_114 = lean_string_append(x_109, x_113);
x_115 = lean_string_append(x_114, x_90);
x_60 = x_80;
x_61 = x_106;
x_62 = x_90;
x_63 = x_105;
x_64 = x_81;
x_65 = x_115;
goto block_74;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = l_Lean_IR_EmitC_emitMainFn___closed__43;
x_117 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_116, x_109);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = l_Lean_IR_EmitC_emitMainFn___closed__44;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_string_append(x_120, x_90);
x_60 = x_80;
x_61 = x_106;
x_62 = x_90;
x_63 = x_105;
x_64 = x_81;
x_65 = x_121;
goto block_74;
}
}
block_140:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = l_Lean_IR_EmitC_emitMainFn___closed__45;
x_128 = lean_string_append(x_126, x_127);
x_129 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_130 = lean_string_append(x_128, x_129);
x_131 = l_Lean_IR_EmitC_emitMainFn___closed__46;
x_132 = lean_string_append(x_130, x_131);
x_133 = lean_string_append(x_132, x_129);
if (x_124 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_135 = lean_string_append(x_133, x_134);
x_136 = lean_string_append(x_135, x_129);
x_80 = x_123;
x_81 = x_125;
x_82 = x_136;
goto block_122;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = l_Lean_IR_EmitC_emitMainFn___closed__48;
x_138 = lean_string_append(x_133, x_137);
x_139 = lean_string_append(x_138, x_129);
x_80 = x_123;
x_81 = x_125;
x_82 = x_139;
goto block_122;
}
}
block_157:
{
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec_ref(x_79);
lean_dec_ref(x_1);
x_142 = l_Lean_IR_EmitC_emitMainFn___closed__49;
if (lean_is_scalar(x_78)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_78;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_77);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_78);
x_144 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_144);
x_145 = l_Lean_IR_EmitC_emitMainFn___closed__51;
x_146 = l_Lean_IR_usesModuleFrom(x_144, x_145);
x_147 = l_Lean_IR_EmitC_emitMainFn___closed__52;
x_148 = lean_string_append(x_77, x_147);
x_149 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_150 = lean_string_append(x_148, x_149);
if (x_146 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = l_Lean_IR_EmitC_emitMainFn___closed__53;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_string_append(x_152, x_149);
x_123 = x_144;
x_124 = x_146;
x_125 = x_1;
x_126 = x_153;
goto block_140;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = l_Lean_IR_EmitC_emitMainFn___closed__54;
x_155 = lean_string_append(x_150, x_154);
x_156 = lean_string_append(x_155, x_149);
x_123 = x_144;
x_124 = x_146;
x_125 = x_1;
x_126 = x_156;
goto block_140;
}
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_76);
lean_dec_ref(x_1);
x_163 = !lean_is_exclusive(x_75);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_75, 0);
lean_dec(x_164);
x_165 = l_Lean_IR_EmitC_emitMainFn___closed__55;
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 0, x_165);
return x_75;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_75, 1);
lean_inc(x_166);
lean_dec(x_75);
x_167 = l_Lean_IR_EmitC_emitMainFn___closed__55;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec_ref(x_1);
x_169 = !lean_is_exclusive(x_75);
if (x_169 == 0)
{
return x_75;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_75, 0);
x_171 = lean_ctor_get(x_75, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_75);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
block_40:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec_ref(x_8);
x_12 = lean_string_append(x_6, x_11);
lean_dec_ref(x_11);
x_13 = l_Lean_IR_EmitC_emitMainFn___closed__0;
x_14 = l_Lean_IR_EmitC_emitMainFn___closed__1;
x_15 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_16 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_17 = l_Lean_IR_EmitC_emitMainFn___closed__4;
lean_inc_ref(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_27, x_10);
lean_dec_ref(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_string_append(x_30, x_7);
lean_dec_ref(x_7);
x_33 = lean_box(0);
x_34 = lean_string_append(x_32, x_3);
lean_dec_ref(x_3);
lean_ctor_set(x_28, 1, x_34);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_string_append(x_35, x_7);
lean_dec_ref(x_7);
x_37 = lean_box(0);
x_38 = lean_string_append(x_36, x_3);
lean_dec_ref(x_3);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
block_58:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = l_Lean_ConstantInfo_type(x_47);
lean_dec_ref(x_47);
x_49 = l_Lean_Expr_getForallBody(x_48);
lean_dec_ref(x_48);
x_50 = l_Lean_Expr_appArg_x21(x_49);
lean_dec_ref(x_49);
x_51 = l_Lean_IR_EmitC_emitMainFn___closed__5;
x_52 = l_Lean_IR_EmitC_emitMainFn___closed__6;
x_53 = l_Lean_Expr_constName_x3f(x_50);
lean_dec_ref(x_50);
x_54 = l_Lean_IR_EmitC_emitMainFn___closed__9;
x_55 = l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1(x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_IR_EmitC_emitMainFn___closed__10;
x_3 = x_42;
x_4 = x_41;
x_5 = x_51;
x_6 = x_52;
x_7 = x_43;
x_8 = x_45;
x_9 = x_44;
x_10 = x_46;
x_11 = x_56;
goto block_40;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_IR_EmitC_emitMainFn___closed__11;
x_3 = x_42;
x_4 = x_41;
x_5 = x_51;
x_6 = x_52;
x_7 = x_43;
x_8 = x_45;
x_9 = x_44;
x_10 = x_46;
x_11 = x_57;
goto block_40;
}
}
block_74:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_66 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_62);
x_69 = 0;
x_70 = l_Lean_Environment_find_x3f(x_60, x_59, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_IR_EmitC_emitMainFn___closed__15;
x_72 = l_panic___at___00Lean_IR_EmitC_emitMainFn_spec__2(x_71);
x_41 = x_61;
x_42 = x_62;
x_43 = x_66;
x_44 = x_63;
x_45 = x_64;
x_46 = x_68;
x_47 = x_72;
goto block_58;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec_ref(x_70);
x_41 = x_61;
x_42 = x_62;
x_43 = x_66;
x_44 = x_63;
x_45 = x_64;
x_46 = x_68;
x_47 = x_73;
goto block_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_hasMainFn___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_IR_Decl_name(x_1);
x_3 = l_Lean_IR_EmitC_toCName___closed__1;
x_4 = lean_name_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_EmitC_hasMainFn___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_hasMainFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_hasMainFn___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_IR_EmitC_hasMainFn___closed__0;
x_5 = l_Lean_IR_getDecls(x_3);
x_6 = l_List_any___redArg(x_5, x_4);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc_ref(x_1);
x_3 = l_Lean_IR_EmitC_hasMainFn(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = l_Lean_IR_EmitC_emitMainFn(x_1, x_12);
return x_13;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("meta ", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("public ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_24; lean_object* x_25; lean_object* x_33; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_9 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
if (x_8 == 0)
{
lean_object* x_38; 
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1;
x_33 = x_38;
goto block_37;
}
else
{
lean_object* x_39; 
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__4;
x_33 = x_39;
goto block_37;
}
block_23:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_12, x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec_ref(x_15);
x_17 = lean_string_append(x_9, x_16);
lean_dec_ref(x_16);
x_18 = lean_box(0);
x_19 = lean_string_append(x_5, x_17);
lean_dec_ref(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
x_4 = x_18;
x_5 = x_19;
goto _start;
}
block_32:
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_27 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0;
x_29 = lean_string_append(x_27, x_28);
if (x_26 == 0)
{
lean_object* x_30; 
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1;
x_10 = x_29;
x_11 = x_30;
goto block_23;
}
else
{
lean_object* x_31; 
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2;
x_10 = x_29;
x_11 = x_31;
goto block_23;
}
}
block_37:
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 2);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1;
x_24 = x_33;
x_25 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3;
x_24 = x_33;
x_25 = x_36;
goto block_32;
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_5);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#include <lean/lean.h>", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#if defined(__clang__)", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#pragma clang diagnostic ignored \"-Wunused-parameter\"", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#pragma clang diagnostic ignored \"-Wunused-label\"", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#elif defined(__GNUC__) && !defined(__CLANG__)", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#pragma GCC diagnostic ignored \"-Wunused-parameter\"", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#pragma GCC diagnostic ignored \"-Wunused-label\"", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"", 58, 58);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#endif", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#ifdef __cplusplus", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extern \"C\" {", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__11;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__12;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__13;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__14;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__15;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__16;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__17;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__18;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__19;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__20;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("// Lean compiler output", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("// Module: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("// Imports:", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = l_Lean_IR_EmitC_emitFileHeader___closed__22;
x_18 = lean_string_append(x_2, x_17);
x_19 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_EmitC_emitFileHeader___closed__23;
x_22 = 1;
x_23 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_16, x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec_ref(x_23);
x_25 = lean_string_append(x_20, x_24);
lean_dec_ref(x_24);
x_26 = lean_string_append(x_25, x_19);
x_27 = l_Lean_IR_EmitC_emitFileHeader___closed__24;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_Environment_imports(x_15);
lean_dec_ref(x_15);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec_ref(x_29);
x_3 = x_28;
goto block_11;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(0);
x_34 = lean_nat_dec_le(x_31, x_31);
if (x_34 == 0)
{
if (x_32 == 0)
{
lean_dec_ref(x_29);
x_3 = x_28;
goto block_11;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_31);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(x_29, x_35, x_36, x_33, x_28);
lean_dec_ref(x_29);
x_12 = x_37;
goto block_14;
}
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_31);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(x_29, x_38, x_39, x_33, x_28);
lean_dec_ref(x_29);
x_12 = x_40;
goto block_14;
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Lean_IR_EmitC_emitFileHeader___closed__0;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_string_append(x_7, x_4);
x_9 = l_Lean_IR_EmitC_emitFileHeader___closed__21;
x_10 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_9, x_8);
return x_10;
}
block_14:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_3 = x_13;
goto block_11;
}
else
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__11;
x_2 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1;
x_3 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileFooter___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown variable '", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0;
x_4 = l_Lean_IR_EmitC_argToCString___closed__0;
x_5 = l_Nat_reprFast(x_1);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = lean_string_append(x_3, x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_IR_EmitC_getDecl___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_throwUnknownVar___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_throwUnknownVar(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_IR_instBEqJoinPointId_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_IR_instHashableJoinPointId_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_getJPParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown join point", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_EmitC_getJPParams___closed__0;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getJPParams(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_declareVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("; ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_EmitC_toCType(x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_EmitC_argToCString___closed__0;
x_13 = l_Nat_reprFast(x_1);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_11, x_14);
lean_dec_ref(x_14);
x_16 = l_Lean_IR_EmitC_declareVar___closed__0;
x_17 = lean_box(0);
x_18 = lean_string_append(x_15, x_16);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_17);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_argToCString___closed__0;
x_25 = l_Nat_reprFast(x_1);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_27 = lean_string_append(x_23, x_26);
lean_dec_ref(x_26);
x_28 = l_Lean_IR_EmitC_declareVar___closed__0;
x_29 = lean_box(0);
x_30 = lean_string_append(x_27, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_declareVar(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_IR_EmitC_declareVar(x_9, x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_6 = x_13;
goto _start;
}
else
{
return x_11;
}
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
if (x_7 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0(x_1, x_11, x_12, x_6, x_2, x_3);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0(x_1, x_14, x_15, x_6, x_2, x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_declareParams(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
x_9 = l_Lean_IR_isTailCallTo(x_8, x_1);
lean_dec_ref(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_IR_EmitC_declareVar(x_5, x_6, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_1 = x_7;
x_2 = x_12;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_box(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = l_Lean_IR_EmitC_declareParams(x_20, x_3, x_4);
if (lean_obj_tag(x_22) == 0)
{
if (x_2 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_20);
lean_dec_ref(x_20);
x_26 = lean_nat_dec_lt(x_24, x_25);
x_1 = x_21;
x_2 = x_26;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_28; 
lean_dec_ref(x_20);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec_ref(x_22);
x_1 = x_21;
x_4 = x_28;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec_ref(x_20);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
default: 
{
uint8_t x_34; 
x_34 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_box(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_4);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_IR_EmitC_declareVars(x_1, x_5, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_optionLikePath___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_optionLikePath___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_optionLikePath(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = l_Lean_IR_EmitC_optionLikePath___closed__1;
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___redArg(x_5, x_4, x_8, x_9, x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 0)
{
return x_7;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
return x_12;
}
}
case 12:
{
goto block_3;
}
case 7:
{
goto block_3;
}
case 8:
{
goto block_3;
}
default: 
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
}
block_3:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_optionLikePath___closed__0;
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_5, x_1);
if (x_7 == 0)
{
lean_dec(x_5);
lean_inc_ref(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget_borrowed(x_2, x_5);
x_9 = l_Lean_IR_EmitC_optionLikePath(x_8);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
{
lean_object* _tmp_4 = x_21;
lean_object* _tmp_5 = x_4;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_optionLikePath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_optionLikePath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_optionLikePath_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_optionLike_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fget_borrowed(x_2, x_7);
if (lean_obj_tag(x_8) == 10)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 1);
x_10 = lean_ctor_get(x_8, 2);
x_11 = lean_ctor_get(x_8, 3);
x_12 = lean_array_get_size(x_9);
x_13 = lean_nat_dec_eq(x_12, x_7);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_10, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_11, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_array_fget_borrowed(x_2, x_19);
x_21 = l_Lean_IR_EmitC_optionLikePath(x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_box(0);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_optionLike_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_optionLike_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_8 = l_Nat_reprFast(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_string_append(x_2, x_9);
lean_dec_ref(x_9);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitPath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".cs.c1", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_IR_EmitC_emitPath___closed__0;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0___redArg(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitPath(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitPath_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTag___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" != 0", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".tag", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTag___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_obj_tag(", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_isObj(x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_IR_IRType_isStruct(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(0);
x_8 = l_Lean_IR_EmitC_argToCString___closed__0;
x_9 = l_Nat_reprFast(x_1);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = lean_string_append(x_4, x_10);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_IR_EmitC_optionLike_x3f(x_2);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_EmitC_argToCString___closed__0;
x_16 = l_Nat_reprFast(x_1);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = lean_string_append(x_4, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_EmitC_emitPath(x_14, x_3, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Lean_IR_EmitC_emitTag___closed__0;
x_24 = lean_box(0);
x_25 = lean_string_append(x_21, x_23);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = l_Lean_IR_EmitC_emitTag___closed__0;
x_28 = lean_box(0);
x_29 = lean_string_append(x_26, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
x_31 = l_Lean_IR_EmitC_argToCString___closed__0;
x_32 = l_Nat_reprFast(x_1);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = lean_string_append(x_4, x_33);
lean_dec_ref(x_33);
x_35 = l_Lean_IR_EmitC_emitTag___closed__1;
x_36 = lean_box(0);
x_37 = lean_string_append(x_34, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = l_Lean_IR_EmitC_emitTag___closed__2;
x_40 = lean_string_append(x_4, x_39);
x_41 = l_Lean_IR_EmitC_argToCString___closed__0;
x_42 = l_Nat_reprFast(x_1);
x_43 = lean_string_append(x_41, x_42);
lean_dec_ref(x_42);
x_44 = lean_string_append(x_40, x_43);
lean_dec_ref(x_43);
x_45 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_46 = lean_box(0);
x_47 = lean_string_append(x_44, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fget(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_array_fget_borrowed(x_1, x_12);
x_14 = l_Lean_IR_Alt_body(x_13);
lean_ctor_set(x_7, 1, x_14);
lean_ctor_set(x_7, 0, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_array_fget_borrowed(x_1, x_20);
x_22 = l_Lean_IR_Alt_body(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_7);
x_26 = lean_box(0);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_isIf(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_needsRC(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 8:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
return x_7;
}
else
{
if (x_7 == 0)
{
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_EmitC_needsRC_spec__0(x_4, x_8, x_9);
return x_10;
}
}
}
case 10:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
return x_14;
}
else
{
if (x_14 == 0)
{
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_13);
x_17 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_EmitC_needsRC_spec__0(x_11, x_15, x_16);
return x_17;
}
}
}
default: 
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_EmitC_needsRC_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_IR_EmitC_needsRC(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
return x_6;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_EmitC_needsRC_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_EmitC_needsRC_spec__0(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_needsRC___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_EmitC_needsRC(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structIncFnPrefix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_l_struct_inc_", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structIncFnPrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_structIncFnPrefix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structDecFnPrefix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_l_struct_dec_", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structDecFnPrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_structDecFnPrefix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_l_struct_reshape_", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structReshapeFnPrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structBoxFnPrefix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_l_struct_box_", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structBoxFnPrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_structBoxFnPrefix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structUnboxFnPrefix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_l_struct_unbox_", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_structUnboxFnPrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_structUnboxFnPrefix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIncOfType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(");", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIncOfType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_inc_ref_n", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIncOfType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_inc_ref", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIncOfType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_inc_n", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIncOfType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_inc", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIncOfType(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_16; uint8_t x_21; lean_object* x_22; 
x_21 = l_Lean_IR_IRType_isStruct(x_2);
if (x_21 == 0)
{
if (x_4 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_dec_eq(x_3, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Lean_IR_EmitC_emitIncOfType___closed__1;
x_22 = x_32;
goto block_29;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_IR_EmitC_emitIncOfType___closed__2;
x_22 = x_33;
goto block_29;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_dec_eq(x_3, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_IR_EmitC_emitIncOfType___closed__3;
x_22 = x_36;
goto block_29;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_IR_EmitC_emitIncOfType___closed__4;
x_22 = x_37;
goto block_29;
}
}
}
else
{
uint8_t x_38; 
x_38 = l_Lean_IR_EmitC_needsRC(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_41 = lean_ctor_get(x_6, 6);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_42, x_41, x_2);
x_44 = l_Lean_IR_EmitC_structIncFnPrefix___closed__0;
x_45 = lean_string_append(x_7, x_44);
x_46 = l_Nat_reprFast(x_43);
x_47 = lean_string_append(x_45, x_46);
lean_dec_ref(x_46);
x_48 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_1);
x_51 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_5);
x_54 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_57 = lean_box(0);
x_58 = lean_string_append(x_55, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_12 = lean_box(0);
x_13 = lean_string_append(x_10, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
block_20:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_5);
x_8 = x_19;
goto block_15;
}
block_29:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_string_append(x_7, x_22);
lean_dec_ref(x_22);
x_24 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_1);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_dec_eq(x_3, x_27);
if (x_28 == 0)
{
x_16 = x_26;
goto block_20;
}
else
{
if (x_21 == 0)
{
x_8 = x_26;
goto block_15;
}
else
{
x_16 = x_26;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIncOfType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l_Lean_IR_EmitC_emitIncOfType(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__3;
x_5 = lean_panic_fn(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_IR_instBEqVarId_beq(x_6, x_2);
if (x_9 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_IR_instHashableVarId_hash(x_3);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_4, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___redArg(x_1, x_3, x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 5);
x_7 = lean_box(0);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_7, x_6, x_1);
x_9 = l_Lean_IR_EmitC_argToCString___closed__0;
x_10 = l_Nat_reprFast(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
lean_inc(x_2);
x_12 = l_Nat_reprFast(x_2);
x_13 = l_Lean_IR_EmitC_emitIncOfType(x_11, x_8, x_2, x_3, x_12, x_4, x_5);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_8);
lean_dec_ref(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitInc(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_dec_ref", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_dec", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_22; 
x_22 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__0;
x_11 = x_22;
goto block_21;
}
else
{
lean_object* x_23; 
x_23 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__1;
x_11 = x_23;
goto block_21;
}
block_21:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_string_append(x_4, x_11);
lean_dec_ref(x_11);
x_13 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_1);
x_16 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_3 = x_10;
x_4 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg(x_1, x_5, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecOfType(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isStruct(x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg(x_1, x_4, x_3, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = l_Lean_IR_EmitC_needsRC(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_13, x_12, x_2);
x_15 = l_Lean_IR_EmitC_structDecFnPrefix___closed__0;
x_16 = lean_string_append(x_6, x_15);
x_17 = l_Nat_reprFast(x_14);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_1);
x_22 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_25 = lean_box(0);
x_26 = lean_string_append(x_23, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecOfType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l_Lean_IR_EmitC_emitDecOfType(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 5);
x_7 = lean_box(0);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_7, x_6, x_1);
x_9 = l_Lean_IR_EmitC_argToCString___closed__0;
x_10 = l_Nat_reprFast(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = l_Lean_IR_EmitC_emitDecOfType(x_11, x_8, x_2, x_3, x_4, x_5);
lean_dec(x_8);
lean_dec_ref(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitDec(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDel___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_free_object(", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Lean_IR_EmitC_emitDel___redArg___closed__0;
x_4 = lean_string_append(x_2, x_3);
x_5 = l_Lean_IR_EmitC_argToCString___closed__0;
x_6 = l_Nat_reprFast(x_1);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec_ref(x_7);
x_9 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_12 = lean_box(0);
x_13 = lean_string_append(x_10, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitDel___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitDel(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSetTag___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set_tag(", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = l_Lean_IR_EmitC_emitSetTag___redArg___closed__0;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Lean_IR_EmitC_argToCString___closed__0;
x_7 = l_Nat_reprFast(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_string_append(x_5, x_8);
lean_dec_ref(x_8);
x_10 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_reprFast(x_2);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_17 = lean_box(0);
x_18 = lean_string_append(x_15, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitSetTag___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitSetTag(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSet___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set(", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = l_Lean_IR_EmitC_emitSet___redArg___closed__0;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Lean_IR_EmitC_argToCString___closed__0;
x_8 = l_Nat_reprFast(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_2);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l_Lean_IR_EmitC_emitArg___redArg(x_3, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_21 = lean_string_append(x_18, x_20);
x_22 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_23 = lean_box(0);
x_24 = lean_string_append(x_21, x_22);
lean_ctor_set(x_16, 1, x_24);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_29 = lean_box(0);
x_30 = lean_string_append(x_27, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSet___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSet(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitOffset___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sizeof(void*)*", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitOffset___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" + ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = l_Nat_reprFast(x_2);
x_8 = lean_string_append(x_3, x_7);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_IR_EmitC_emitOffset___redArg___closed__0;
x_11 = lean_string_append(x_3, x_10);
x_12 = l_Nat_reprFast(x_1);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = lean_nat_dec_lt(x_4, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Lean_IR_EmitC_emitOffset___redArg___closed__1;
x_18 = lean_string_append(x_13, x_17);
x_19 = lean_box(0);
x_20 = l_Nat_reprFast(x_2);
x_21 = lean_string_append(x_18, x_20);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitOffset___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitOffset(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1;
x_2 = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0___closed__0;
x_5 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_2(x_6, x_2, x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".cs.c", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".u[", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("] = ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.EmitC", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.EmitC.emitUSet", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitUSet___closed__5;
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(470u);
x_4 = l_Lean_IR_EmitC_emitUSet___closed__4;
x_5 = l_Lean_IR_EmitC_emitUSet___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set_usize(", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 5);
x_8 = lean_box(0);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_8, x_7, x_1);
if (lean_obj_tag(x_9) == 11)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_array_get(x_8, x_11, x_2);
lean_dec_ref(x_11);
if (lean_obj_tag(x_13) == 10)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_5);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_EmitC_argToCString___closed__0;
x_16 = l_Nat_reprFast(x_1);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = lean_string_append(x_6, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Nat_reprFast(x_2);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_array_get_size(x_14);
lean_dec_ref(x_14);
x_26 = lean_nat_sub(x_3, x_25);
lean_dec(x_3);
x_27 = l_Nat_reprFast(x_26);
x_28 = lean_string_append(x_24, x_27);
lean_dec_ref(x_27);
x_29 = l_Lean_IR_EmitC_emitUSet___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Nat_reprFast(x_4);
x_32 = lean_string_append(x_15, x_31);
lean_dec_ref(x_31);
x_33 = lean_string_append(x_30, x_32);
lean_dec_ref(x_32);
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_37 = lean_box(0);
x_38 = lean_string_append(x_35, x_36);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 1, x_38);
lean_ctor_set(x_9, 0, x_37);
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
lean_free_object(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l_Lean_IR_EmitC_emitUSet___closed__6;
x_40 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_39, x_5, x_6);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_dec(x_9);
x_42 = lean_array_get(x_8, x_41, x_2);
lean_dec_ref(x_41);
if (lean_obj_tag(x_42) == 10)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_5);
x_43 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_IR_EmitC_argToCString___closed__0;
x_45 = l_Nat_reprFast(x_1);
x_46 = lean_string_append(x_44, x_45);
lean_dec_ref(x_45);
x_47 = lean_string_append(x_6, x_46);
lean_dec_ref(x_46);
x_48 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Nat_reprFast(x_2);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_array_get_size(x_43);
lean_dec_ref(x_43);
x_55 = lean_nat_sub(x_3, x_54);
lean_dec(x_3);
x_56 = l_Nat_reprFast(x_55);
x_57 = lean_string_append(x_53, x_56);
lean_dec_ref(x_56);
x_58 = l_Lean_IR_EmitC_emitUSet___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Nat_reprFast(x_4);
x_61 = lean_string_append(x_44, x_60);
lean_dec_ref(x_60);
x_62 = lean_string_append(x_59, x_61);
lean_dec_ref(x_61);
x_63 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_66 = lean_box(0);
x_67 = lean_string_append(x_64, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = l_Lean_IR_EmitC_emitUSet___closed__6;
x_70 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_69, x_5, x_6);
return x_70;
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_9) == 10)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_71 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_71);
lean_dec_ref(x_9);
x_72 = l_Lean_IR_EmitC_argToCString___closed__0;
x_73 = l_Nat_reprFast(x_1);
x_74 = lean_string_append(x_72, x_73);
lean_dec_ref(x_73);
x_75 = lean_string_append(x_6, x_74);
lean_dec_ref(x_74);
x_76 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_array_get_size(x_71);
lean_dec_ref(x_71);
x_79 = lean_nat_sub(x_3, x_78);
lean_dec(x_3);
x_80 = l_Nat_reprFast(x_79);
x_81 = lean_string_append(x_77, x_80);
lean_dec_ref(x_80);
x_82 = l_Lean_IR_EmitC_emitUSet___closed__2;
x_83 = lean_string_append(x_81, x_82);
x_84 = l_Nat_reprFast(x_4);
x_85 = lean_string_append(x_72, x_84);
lean_dec_ref(x_84);
x_86 = lean_string_append(x_83, x_85);
lean_dec_ref(x_85);
x_87 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_88 = lean_string_append(x_86, x_87);
x_89 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_90 = lean_box(0);
x_91 = lean_string_append(x_88, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_9);
x_93 = l_Lean_IR_EmitC_emitUSet___closed__7;
x_94 = lean_string_append(x_6, x_93);
x_95 = l_Lean_IR_EmitC_argToCString___closed__0;
x_96 = l_Nat_reprFast(x_1);
x_97 = lean_string_append(x_95, x_96);
lean_dec_ref(x_96);
x_98 = lean_string_append(x_94, x_97);
lean_dec_ref(x_97);
x_99 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_100 = lean_string_append(x_98, x_99);
x_101 = l_Nat_reprFast(x_3);
x_102 = lean_string_append(x_100, x_101);
lean_dec_ref(x_101);
x_103 = lean_string_append(x_102, x_99);
x_104 = l_Nat_reprFast(x_4);
x_105 = lean_string_append(x_95, x_104);
lean_dec_ref(x_104);
x_106 = lean_string_append(x_103, x_105);
lean_dec_ref(x_105);
x_107 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_108 = lean_string_append(x_106, x_107);
x_109 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_110 = lean_box(0);
x_111 = lean_string_append(x_108, x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*((", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*)(", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".s+", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")) = ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set_float", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set_float32", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set_uint8", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set_uint16", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set_uint32", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set_uint64", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid instruction", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_7, 5);
x_44 = lean_box(0);
x_45 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_44, x_43, x_1);
if (lean_obj_tag(x_45) == 11)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_45);
lean_dec(x_3);
x_46 = l_Lean_IR_EmitC_emitSSet___closed__0;
x_47 = lean_string_append(x_8, x_46);
x_48 = l_Lean_IR_EmitC_toCType(x_6, x_7, x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_Lean_IR_EmitC_argToCString___closed__0;
x_56 = l_Nat_reprFast(x_1);
x_57 = lean_string_append(x_55, x_56);
lean_dec_ref(x_56);
x_58 = lean_string_append(x_54, x_57);
lean_dec_ref(x_57);
x_59 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_60 = lean_string_append(x_58, x_59);
x_61 = l_Nat_reprFast(x_2);
x_62 = lean_string_append(x_60, x_61);
lean_dec_ref(x_61);
x_63 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Nat_reprFast(x_4);
x_66 = lean_string_append(x_64, x_65);
lean_dec_ref(x_65);
x_67 = l_Lean_IR_EmitC_emitSSet___closed__3;
x_68 = lean_string_append(x_66, x_67);
x_69 = l_Nat_reprFast(x_5);
x_70 = lean_string_append(x_55, x_69);
lean_dec_ref(x_69);
x_71 = lean_string_append(x_68, x_70);
lean_dec_ref(x_70);
x_72 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_73 = lean_string_append(x_71, x_72);
x_74 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_box(0);
lean_ctor_set(x_48, 1, x_75);
lean_ctor_set(x_48, 0, x_76);
return x_48;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_77 = lean_ctor_get(x_48, 0);
x_78 = lean_ctor_get(x_48, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_48);
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_Lean_IR_EmitC_argToCString___closed__0;
x_83 = l_Nat_reprFast(x_1);
x_84 = lean_string_append(x_82, x_83);
lean_dec_ref(x_83);
x_85 = lean_string_append(x_81, x_84);
lean_dec_ref(x_84);
x_86 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_87 = lean_string_append(x_85, x_86);
x_88 = l_Nat_reprFast(x_2);
x_89 = lean_string_append(x_87, x_88);
lean_dec_ref(x_88);
x_90 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_91 = lean_string_append(x_89, x_90);
x_92 = l_Nat_reprFast(x_4);
x_93 = lean_string_append(x_91, x_92);
lean_dec_ref(x_92);
x_94 = l_Lean_IR_EmitC_emitSSet___closed__3;
x_95 = lean_string_append(x_93, x_94);
x_96 = l_Nat_reprFast(x_5);
x_97 = lean_string_append(x_82, x_96);
lean_dec_ref(x_96);
x_98 = lean_string_append(x_95, x_97);
lean_dec_ref(x_97);
x_99 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_100 = lean_string_append(x_98, x_99);
x_101 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_45) == 10)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec_ref(x_45);
lean_dec(x_3);
x_105 = l_Lean_IR_EmitC_emitSSet___closed__0;
x_106 = lean_string_append(x_8, x_105);
x_107 = l_Lean_IR_EmitC_toCType(x_6, x_7, x_106);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
x_111 = lean_string_append(x_110, x_109);
lean_dec(x_109);
x_112 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_113 = lean_string_append(x_111, x_112);
x_114 = l_Lean_IR_EmitC_argToCString___closed__0;
x_115 = l_Nat_reprFast(x_1);
x_116 = lean_string_append(x_114, x_115);
lean_dec_ref(x_115);
x_117 = lean_string_append(x_113, x_116);
lean_dec_ref(x_116);
x_118 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_119 = lean_string_append(x_117, x_118);
x_120 = l_Nat_reprFast(x_4);
x_121 = lean_string_append(x_119, x_120);
lean_dec_ref(x_120);
x_122 = l_Lean_IR_EmitC_emitSSet___closed__3;
x_123 = lean_string_append(x_121, x_122);
x_124 = l_Nat_reprFast(x_5);
x_125 = lean_string_append(x_114, x_124);
lean_dec_ref(x_124);
x_126 = lean_string_append(x_123, x_125);
lean_dec_ref(x_125);
x_127 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_128 = lean_string_append(x_126, x_127);
x_129 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_box(0);
lean_ctor_set(x_107, 1, x_130);
lean_ctor_set(x_107, 0, x_131);
return x_107;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_132 = lean_ctor_get(x_107, 0);
x_133 = lean_ctor_get(x_107, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_107);
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_135 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_136 = lean_string_append(x_134, x_135);
x_137 = l_Lean_IR_EmitC_argToCString___closed__0;
x_138 = l_Nat_reprFast(x_1);
x_139 = lean_string_append(x_137, x_138);
lean_dec_ref(x_138);
x_140 = lean_string_append(x_136, x_139);
lean_dec_ref(x_139);
x_141 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_142 = lean_string_append(x_140, x_141);
x_143 = l_Nat_reprFast(x_4);
x_144 = lean_string_append(x_142, x_143);
lean_dec_ref(x_143);
x_145 = l_Lean_IR_EmitC_emitSSet___closed__3;
x_146 = lean_string_append(x_144, x_145);
x_147 = l_Nat_reprFast(x_5);
x_148 = lean_string_append(x_137, x_147);
lean_dec_ref(x_147);
x_149 = lean_string_append(x_146, x_148);
lean_dec_ref(x_148);
x_150 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_151 = lean_string_append(x_149, x_150);
x_152 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_153 = lean_string_append(x_151, x_152);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_dec(x_45);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_156; lean_object* x_157; 
x_156 = l_Lean_IR_EmitC_emitSSet___closed__4;
x_157 = lean_string_append(x_8, x_156);
x_9 = x_157;
goto block_42;
}
case 9:
{
lean_object* x_158; lean_object* x_159; 
x_158 = l_Lean_IR_EmitC_emitSSet___closed__5;
x_159 = lean_string_append(x_8, x_158);
x_9 = x_159;
goto block_42;
}
case 1:
{
lean_object* x_160; lean_object* x_161; 
x_160 = l_Lean_IR_EmitC_emitSSet___closed__6;
x_161 = lean_string_append(x_8, x_160);
x_9 = x_161;
goto block_42;
}
case 2:
{
lean_object* x_162; lean_object* x_163; 
x_162 = l_Lean_IR_EmitC_emitSSet___closed__7;
x_163 = lean_string_append(x_8, x_162);
x_9 = x_163;
goto block_42;
}
case 3:
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lean_IR_EmitC_emitSSet___closed__8;
x_165 = lean_string_append(x_8, x_164);
x_9 = x_165;
goto block_42;
}
case 4:
{
lean_object* x_166; lean_object* x_167; 
x_166 = l_Lean_IR_EmitC_emitSSet___closed__9;
x_167 = lean_string_append(x_8, x_166);
x_9 = x_167;
goto block_42;
}
default: 
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_168 = l_Lean_IR_EmitC_emitSSet___closed__10;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_8);
return x_169;
}
}
}
}
block_42:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_EmitC_argToCString___closed__0;
x_13 = l_Nat_reprFast(x_1);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_11, x_14);
lean_dec_ref(x_14);
x_16 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_EmitC_emitOffset___redArg(x_3, x_4, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_string_append(x_20, x_16);
x_23 = l_Nat_reprFast(x_5);
x_24 = lean_string_append(x_12, x_23);
lean_dec_ref(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_29 = lean_box(0);
x_30 = lean_string_append(x_27, x_28);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_string_append(x_31, x_16);
x_33 = l_Nat_reprFast(x_5);
x_34 = lean_string_append(x_12, x_33);
lean_dec_ref(x_33);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
x_36 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_39 = lean_box(0);
x_40 = lean_string_append(x_37, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_EmitC_emitSSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget_borrowed(x_1, x_13);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_array_fget_borrowed(x_2, x_13);
lean_dec(x_13);
x_17 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_15);
x_18 = l_Nat_reprFast(x_15);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_5, x_19);
lean_dec_ref(x_19);
x_21 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_22 = lean_string_append(x_20, x_21);
lean_inc(x_16);
x_23 = l_Lean_IR_EmitC_emitArg___redArg(x_16, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_28 = lean_string_append(x_26, x_27);
x_4 = x_11;
x_5 = x_28;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitJmp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid goto", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitJmp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goto ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitJmp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("block_", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_getJPParams(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_array_get_size(x_7);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = l_Lean_IR_EmitC_emitJmp___closed__0;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_free_object(x_5);
x_13 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(x_7, x_2, x_9, x_9, x_8);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l_Lean_IR_EmitC_emitJmp___closed__1;
x_18 = lean_string_append(x_15, x_17);
x_19 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_20 = l_Nat_reprFast(x_1);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_26 = lean_box(0);
x_27 = lean_string_append(x_24, x_25);
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = l_Lean_IR_EmitC_emitJmp___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_32 = l_Nat_reprFast(x_1);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = lean_string_append(x_30, x_33);
lean_dec_ref(x_33);
x_35 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_38 = lean_box(0);
x_39 = lean_string_append(x_36, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_43 = lean_array_get_size(x_2);
x_44 = lean_array_get_size(x_41);
x_45 = lean_nat_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_41);
lean_dec(x_1);
x_46 = l_Lean_IR_EmitC_emitJmp___closed__0;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_48 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(x_41, x_2, x_43, x_43, x_42);
lean_dec(x_41);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = l_Lean_IR_EmitC_emitJmp___closed__1;
x_52 = lean_string_append(x_49, x_51);
x_53 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_54 = l_Nat_reprFast(x_1);
x_55 = lean_string_append(x_53, x_54);
lean_dec_ref(x_54);
x_56 = lean_string_append(x_52, x_55);
lean_dec_ref(x_55);
x_57 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_60 = lean_box(0);
x_61 = lean_string_append(x_58, x_59);
if (lean_is_scalar(x_50)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_50;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_5);
if (x_63 == 0)
{
return x_5;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_5, 0);
x_65 = lean_ctor_get(x_5, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_5);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitJmp(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_IR_EmitC_argToCString___closed__0;
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
x_6 = lean_string_append(x_2, x_5);
lean_dec_ref(x_5);
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_8 = lean_box(0);
x_9 = lean_string_append(x_6, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLhs(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_19 = lean_nat_dec_lt(x_5, x_12);
if (x_19 == 0)
{
x_13 = x_4;
goto block_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_21 = lean_string_append(x_4, x_20);
x_13 = x_21;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget_borrowed(x_1, x_12);
lean_dec(x_12);
lean_inc(x_14);
x_15 = l_Lean_IR_EmitC_emitArg___redArg(x_14, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_3 = x_10;
x_4 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(x_1, x_4, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArgs(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCtorScalarSize___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sizeof(size_t)*", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_2, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_IR_EmitC_emitCtorScalarSize___redArg___closed__0;
x_8 = lean_string_append(x_3, x_7);
x_9 = l_Nat_reprFast(x_1);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitOffset___redArg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_box(0);
x_14 = l_Nat_reprFast(x_2);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_17 = l_Lean_IR_EmitC_emitCtorScalarSize___redArg___closed__0;
x_18 = lean_string_append(x_3, x_17);
x_19 = lean_box(0);
x_20 = l_Nat_reprFast(x_1);
x_21 = lean_string_append(x_18, x_20);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = l_Nat_reprFast(x_2);
x_25 = lean_string_append(x_3, x_24);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorScalarSize___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorScalarSize(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_alloc_ctor(", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0;
x_8 = lean_string_append(x_2, x_7);
x_9 = l_Nat_reprFast(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_4);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l_Lean_IR_EmitC_emitCtorScalarSize___redArg(x_5, x_6, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_21 = lean_string_append(x_18, x_20);
x_22 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_23 = lean_box(0);
x_24 = lean_string_append(x_21, x_22);
lean_ctor_set(x_16, 1, x_24);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_29 = lean_box(0);
x_30 = lean_string_append(x_27, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitAllocCtor___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitAllocCtor(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_IR_EmitC_emitSet___redArg___closed__0;
x_15 = lean_string_append(x_5, x_14);
x_16 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_1);
x_17 = l_Nat_reprFast(x_1);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = lean_string_append(x_15, x_18);
lean_dec_ref(x_18);
x_20 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_21 = lean_string_append(x_19, x_20);
lean_inc(x_13);
x_22 = l_Nat_reprFast(x_13);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = lean_string_append(x_23, x_20);
x_25 = lean_array_fget_borrowed(x_2, x_13);
lean_dec(x_13);
lean_inc(x_25);
x_26 = l_Lean_IR_EmitC_emitArg___redArg(x_25, x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_31 = lean_string_append(x_29, x_30);
x_4 = x_11;
x_5 = x_31;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(x_1, x_2, x_5, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_7, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_2);
x_18 = lean_array_get_borrowed(x_2, x_3, x_7);
switch (lean_obj_tag(x_18)) {
case 6:
{
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
case 13:
{
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_5);
x_20 = l_Nat_reprFast(x_5);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_9, x_21);
lean_dec_ref(x_21);
x_23 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_24 = lean_string_append(x_22, x_23);
lean_inc(x_7);
x_25 = l_Nat_reprFast(x_7);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_27 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_array_fget_borrowed(x_6, x_7);
lean_inc(x_29);
x_30 = l_Lean_IR_EmitC_emitArg___redArg(x_29, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_35 = lean_string_append(x_33, x_34);
x_10 = x_4;
x_11 = x_35;
goto block_15;
}
else
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_30;
}
}
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
x_8 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_8, x_1);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_2);
x_19 = lean_array_get_borrowed(x_2, x_3, x_8);
switch (lean_obj_tag(x_19)) {
case 6:
{
x_11 = x_4;
x_12 = x_10;
goto block_16;
}
case 13:
{
x_11 = x_4;
x_12 = x_10;
goto block_16;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_6, 1);
x_21 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_5);
x_22 = l_Nat_reprFast(x_5);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = lean_string_append(x_10, x_23);
lean_dec_ref(x_23);
x_25 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_26 = lean_string_append(x_24, x_25);
lean_inc(x_20);
x_27 = l_Nat_reprFast(x_20);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_30 = lean_string_append(x_28, x_29);
lean_inc(x_8);
x_31 = l_Nat_reprFast(x_8);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_array_fget_borrowed(x_7, x_8);
lean_inc(x_35);
x_36 = l_Lean_IR_EmitC_emitArg___redArg(x_35, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_41 = lean_string_append(x_39, x_40);
x_11 = x_4;
x_12 = x_41;
goto block_16;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_36;
}
}
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_8 = x_14;
x_9 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCtor___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box(", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.EmitC.emitCtor", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCtor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitUSet___closed__5;
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_unsigned_to_nat(537u);
x_4 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_5 = l_Lean_IR_EmitC_emitUSet___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCtor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = 0;", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCtor___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".tag = ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_31; lean_object* x_32; lean_object* x_41; 
x_41 = lean_box(0);
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_60; 
x_42 = lean_ctor_get(x_2, 1);
x_60 = l_Lean_IR_EmitC_optionLike_x3f(x_2);
if (lean_obj_tag(x_60) == 1)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_3, 1);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_dec(x_61);
x_43 = x_5;
x_44 = x_6;
goto block_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec_ref(x_3);
x_65 = l_Lean_IR_EmitC_argToCString___closed__0;
x_66 = l_Nat_reprFast(x_1);
x_67 = lean_string_append(x_65, x_66);
lean_dec_ref(x_66);
x_68 = lean_string_append(x_6, x_67);
lean_dec_ref(x_67);
x_69 = l_Lean_IR_EmitC_emitPath(x_61, x_5, x_68);
lean_dec_ref(x_5);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_69, 1);
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = l_Lean_IR_EmitC_emitCtor___closed__3;
x_74 = lean_string_append(x_71, x_73);
x_75 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_76 = lean_string_append(x_74, x_75);
x_77 = lean_box(0);
lean_ctor_set(x_69, 1, x_76);
lean_ctor_set(x_69, 0, x_77);
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_dec(x_69);
x_79 = l_Lean_IR_EmitC_emitCtor___closed__3;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_60);
x_85 = lean_ctor_get(x_3, 1);
x_86 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_1);
x_87 = l_Nat_reprFast(x_1);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
x_89 = lean_string_append(x_6, x_88);
lean_dec_ref(x_88);
x_90 = l_Lean_IR_EmitC_emitCtor___closed__4;
x_91 = lean_string_append(x_89, x_90);
lean_inc(x_85);
x_92 = l_Nat_reprFast(x_85);
x_93 = lean_string_append(x_91, x_92);
lean_dec_ref(x_92);
x_94 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_95 = lean_string_append(x_93, x_94);
x_96 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_97 = lean_string_append(x_95, x_96);
x_43 = x_5;
x_44 = x_97;
goto block_59;
}
block_59:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_array_get_borrowed(x_41, x_42, x_45);
if (lean_obj_tag(x_46) == 10)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_43);
x_47 = lean_ctor_get(x_46, 1);
x_48 = lean_array_get_size(x_4);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_box(0);
x_51 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___redArg(x_48, x_41, x_47, x_50, x_1, x_3, x_4, x_49, x_50, x_44);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
return x_51;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_IR_EmitC_emitCtor___closed__2;
lean_inc_ref(x_43);
x_57 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_56, x_43, x_44);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_31 = x_43;
x_32 = x_58;
goto block_40;
}
else
{
lean_dec_ref(x_43);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_57;
}
}
}
}
else
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_98 = lean_ctor_get(x_2, 1);
x_99 = lean_array_get_size(x_4);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_box(0);
x_102 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___redArg(x_99, x_41, x_98, x_101, x_1, x_4, x_100, x_101, x_6);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
return x_102;
}
}
else
{
x_31 = x_5;
x_32 = x_6;
goto block_40;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_IR_EmitC_emitAllocCtor___redArg(x_3, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_4, x_7, x_10);
lean_dec_ref(x_7);
return x_11;
}
block_30:
{
if (x_15 == 0)
{
x_7 = x_13;
x_8 = x_14;
goto block_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
x_7 = x_13;
x_8 = x_14;
goto block_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_3);
lean_dec(x_1);
x_20 = l_Lean_IR_EmitC_emitCtor___closed__0;
x_21 = lean_string_append(x_14, x_20);
x_22 = l_Nat_reprFast(x_16);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_27 = lean_box(0);
x_28 = lean_string_append(x_25, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
block_40:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_1);
x_33 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_ctor_get(x_3, 3);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_eq(x_35, x_37);
if (x_38 == 0)
{
x_13 = x_31;
x_14 = x_34;
x_15 = x_38;
goto block_30;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_eq(x_36, x_37);
x_13 = x_31;
x_14 = x_34;
x_15 = x_39;
goto block_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitCtor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitCtor_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" lean_ctor_release(", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0;
x_14 = lean_string_append(x_4, x_13);
x_15 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_1);
x_16 = l_Nat_reprFast(x_1);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = lean_string_append(x_14, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Nat_reprFast(x_12);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_26 = lean_string_append(x_24, x_25);
x_3 = x_10;
x_4 = x_26;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (lean_is_exclusive(", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")) {", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" lean_dec_ref(", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box(0);", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_6 = l_Lean_IR_EmitC_emitReset___closed__0;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_3);
x_9 = l_Nat_reprFast(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = lean_string_append(x_7, x_10);
x_12 = l_Lean_IR_EmitC_emitReset___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_15 = lean_string_append(x_13, x_14);
lean_inc(x_2);
x_16 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(x_3, x_2, x_2, x_15);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_1);
x_20 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_21, x_10);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_14);
x_26 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_14);
x_29 = l_Lean_IR_EmitC_emitReset___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_10);
lean_dec_ref(x_10);
x_32 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_14);
x_35 = lean_string_append(x_34, x_18);
x_36 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = l_Lean_IR_EmitC_emitReset___closed__3;
x_41 = lean_string_append(x_38, x_40);
x_42 = lean_string_append(x_41, x_14);
x_43 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_box(0);
x_46 = lean_string_append(x_44, x_14);
lean_ctor_set(x_36, 1, x_46);
lean_ctor_set(x_36, 0, x_45);
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_dec(x_36);
x_48 = l_Lean_IR_EmitC_emitReset___closed__3;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_14);
x_51 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_box(0);
x_54 = lean_string_append(x_52, x_14);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitReset(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReuse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (lean_is_scalar(", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReuse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" lean_ctor_set_tag(", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_16 = l_Lean_IR_EmitC_emitReuse___closed__0;
x_17 = lean_string_append(x_7, x_16);
x_18 = l_Lean_IR_EmitC_argToCString___closed__0;
x_19 = l_Nat_reprFast(x_2);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = lean_string_append(x_17, x_20);
x_22 = l_Lean_IR_EmitC_emitReset___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_27 = lean_string_append(x_25, x_26);
lean_inc(x_1);
x_28 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_inc_ref(x_3);
x_30 = l_Lean_IR_EmitC_emitAllocCtor___redArg(x_3, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_24);
x_35 = lean_string_append(x_34, x_26);
lean_inc(x_1);
x_36 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_string_append(x_37, x_20);
lean_dec_ref(x_20);
x_39 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_string_append(x_40, x_24);
if (x_4 == 0)
{
lean_dec_ref(x_3);
x_8 = x_6;
x_9 = x_41;
goto block_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
lean_dec_ref(x_3);
x_43 = l_Lean_IR_EmitC_emitReuse___closed__1;
x_44 = lean_string_append(x_41, x_43);
lean_inc(x_1);
x_45 = l_Nat_reprFast(x_1);
x_46 = lean_string_append(x_18, x_45);
lean_dec_ref(x_45);
x_47 = lean_string_append(x_44, x_46);
lean_dec_ref(x_46);
x_48 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Nat_reprFast(x_42);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_24);
x_8 = x_6;
x_9 = x_54;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_8, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l_Lean_IR_EmitC_emitReuse(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitProj___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_get(", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_box(0);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_12, x_11, x_4);
if (lean_obj_tag(x_13) == 10)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_13);
lean_dec(x_2);
x_14 = l_Lean_IR_EmitC_argToCString___closed__0;
x_15 = l_Nat_reprFast(x_4);
x_16 = lean_string_append(x_14, x_15);
lean_dec_ref(x_15);
x_17 = lean_string_append(x_9, x_16);
lean_dec_ref(x_16);
x_18 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Nat_reprFast(x_3);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_25 = lean_box(0);
x_26 = lean_string_append(x_23, x_24);
lean_ctor_set(x_7, 1, x_26);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
else
{
if (lean_obj_tag(x_13) == 11)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_13);
x_27 = l_Lean_IR_EmitC_argToCString___closed__0;
x_28 = l_Nat_reprFast(x_4);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = lean_string_append(x_9, x_29);
lean_dec_ref(x_29);
x_31 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Nat_reprFast(x_2);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Nat_reprFast(x_3);
x_38 = lean_string_append(x_36, x_37);
lean_dec_ref(x_37);
x_39 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_42 = lean_box(0);
x_43 = lean_string_append(x_40, x_41);
lean_ctor_set(x_7, 1, x_43);
lean_ctor_set(x_7, 0, x_42);
return x_7;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
lean_dec(x_2);
x_44 = l_Lean_IR_EmitC_emitProj___closed__0;
x_45 = lean_string_append(x_9, x_44);
x_46 = l_Lean_IR_EmitC_argToCString___closed__0;
x_47 = l_Nat_reprFast(x_4);
x_48 = lean_string_append(x_46, x_47);
lean_dec_ref(x_47);
x_49 = lean_string_append(x_45, x_48);
lean_dec_ref(x_48);
x_50 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Nat_reprFast(x_3);
x_53 = lean_string_append(x_51, x_52);
lean_dec_ref(x_52);
x_54 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_57 = lean_box(0);
x_58 = lean_string_append(x_55, x_56);
lean_ctor_set(x_7, 1, x_58);
lean_ctor_set(x_7, 0, x_57);
return x_7;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_dec(x_7);
x_60 = lean_ctor_get(x_5, 5);
x_61 = lean_box(0);
x_62 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_61, x_60, x_4);
if (lean_obj_tag(x_62) == 10)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_62);
lean_dec(x_2);
x_63 = l_Lean_IR_EmitC_argToCString___closed__0;
x_64 = l_Nat_reprFast(x_4);
x_65 = lean_string_append(x_63, x_64);
lean_dec_ref(x_64);
x_66 = lean_string_append(x_59, x_65);
lean_dec_ref(x_65);
x_67 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_68 = lean_string_append(x_66, x_67);
x_69 = l_Nat_reprFast(x_3);
x_70 = lean_string_append(x_68, x_69);
lean_dec_ref(x_69);
x_71 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_72 = lean_string_append(x_70, x_71);
x_73 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_74 = lean_box(0);
x_75 = lean_string_append(x_72, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
if (lean_obj_tag(x_62) == 11)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_62);
x_77 = l_Lean_IR_EmitC_argToCString___closed__0;
x_78 = l_Nat_reprFast(x_4);
x_79 = lean_string_append(x_77, x_78);
lean_dec_ref(x_78);
x_80 = lean_string_append(x_59, x_79);
lean_dec_ref(x_79);
x_81 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Nat_reprFast(x_2);
x_84 = lean_string_append(x_82, x_83);
lean_dec_ref(x_83);
x_85 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Nat_reprFast(x_3);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
x_89 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_90 = lean_string_append(x_88, x_89);
x_91 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_92 = lean_box(0);
x_93 = lean_string_append(x_90, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_62);
lean_dec(x_2);
x_95 = l_Lean_IR_EmitC_emitProj___closed__0;
x_96 = lean_string_append(x_59, x_95);
x_97 = l_Lean_IR_EmitC_argToCString___closed__0;
x_98 = l_Nat_reprFast(x_4);
x_99 = lean_string_append(x_97, x_98);
lean_dec_ref(x_98);
x_100 = lean_string_append(x_96, x_99);
lean_dec_ref(x_99);
x_101 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = l_Nat_reprFast(x_3);
x_104 = lean_string_append(x_102, x_103);
lean_dec_ref(x_103);
x_105 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_106 = lean_string_append(x_104, x_105);
x_107 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_108 = lean_box(0);
x_109 = lean_string_append(x_106, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitProj(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUProj___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("];", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.EmitC.emitUProj", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUProj___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitUSet___closed__5;
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(589u);
x_4 = l_Lean_IR_EmitC_emitUProj___closed__1;
x_5 = l_Lean_IR_EmitC_emitUSet___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUProj___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_get_usize(", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_box(0);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_12, x_11, x_4);
if (lean_obj_tag(x_13) == 11)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = lean_array_get(x_12, x_14, x_2);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 10)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_IR_EmitC_argToCString___closed__0;
x_18 = l_Nat_reprFast(x_4);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_9, x_19);
lean_dec_ref(x_19);
x_21 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_reprFast(x_2);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_array_get_size(x_16);
lean_dec_ref(x_16);
x_28 = lean_nat_sub(x_3, x_27);
lean_dec(x_3);
x_29 = l_Nat_reprFast(x_28);
x_30 = lean_string_append(x_26, x_29);
lean_dec_ref(x_29);
x_31 = l_Lean_IR_EmitC_emitUProj___closed__0;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_34 = lean_box(0);
x_35 = lean_string_append(x_32, x_33);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = l_Lean_IR_EmitC_emitUProj___closed__2;
x_37 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_36, x_5, x_9);
return x_37;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 10)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_13);
x_39 = l_Lean_IR_EmitC_argToCString___closed__0;
x_40 = l_Nat_reprFast(x_4);
x_41 = lean_string_append(x_39, x_40);
lean_dec_ref(x_40);
x_42 = lean_string_append(x_9, x_41);
lean_dec_ref(x_41);
x_43 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_array_get_size(x_38);
lean_dec_ref(x_38);
x_46 = lean_nat_sub(x_3, x_45);
lean_dec(x_3);
x_47 = l_Nat_reprFast(x_46);
x_48 = lean_string_append(x_44, x_47);
lean_dec_ref(x_47);
x_49 = l_Lean_IR_EmitC_emitUProj___closed__0;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_52 = lean_box(0);
x_53 = lean_string_append(x_50, x_51);
lean_ctor_set(x_7, 1, x_53);
lean_ctor_set(x_7, 0, x_52);
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_13);
x_54 = l_Lean_IR_EmitC_emitUProj___closed__3;
x_55 = lean_string_append(x_9, x_54);
x_56 = l_Lean_IR_EmitC_argToCString___closed__0;
x_57 = l_Nat_reprFast(x_4);
x_58 = lean_string_append(x_56, x_57);
lean_dec_ref(x_57);
x_59 = lean_string_append(x_55, x_58);
lean_dec_ref(x_58);
x_60 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_61 = lean_string_append(x_59, x_60);
x_62 = l_Nat_reprFast(x_3);
x_63 = lean_string_append(x_61, x_62);
lean_dec_ref(x_62);
x_64 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_65 = lean_string_append(x_63, x_64);
x_66 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_67 = lean_box(0);
x_68 = lean_string_append(x_65, x_66);
lean_ctor_set(x_7, 1, x_68);
lean_ctor_set(x_7, 0, x_67);
return x_7;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_7, 1);
lean_inc(x_69);
lean_dec(x_7);
x_70 = lean_ctor_get(x_5, 5);
x_71 = lean_box(0);
x_72 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_71, x_70, x_4);
if (lean_obj_tag(x_72) == 11)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_73);
lean_dec_ref(x_72);
x_74 = lean_array_get(x_71, x_73, x_2);
lean_dec_ref(x_73);
if (lean_obj_tag(x_74) == 10)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_5);
x_75 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_IR_EmitC_argToCString___closed__0;
x_77 = l_Nat_reprFast(x_4);
x_78 = lean_string_append(x_76, x_77);
lean_dec_ref(x_77);
x_79 = lean_string_append(x_69, x_78);
lean_dec_ref(x_78);
x_80 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_Nat_reprFast(x_2);
x_83 = lean_string_append(x_81, x_82);
lean_dec_ref(x_82);
x_84 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_array_get_size(x_75);
lean_dec_ref(x_75);
x_87 = lean_nat_sub(x_3, x_86);
lean_dec(x_3);
x_88 = l_Nat_reprFast(x_87);
x_89 = lean_string_append(x_85, x_88);
lean_dec_ref(x_88);
x_90 = l_Lean_IR_EmitC_emitUProj___closed__0;
x_91 = lean_string_append(x_89, x_90);
x_92 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_93 = lean_box(0);
x_94 = lean_string_append(x_91, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_74);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = l_Lean_IR_EmitC_emitUProj___closed__2;
x_97 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_96, x_5, x_69);
return x_97;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_72) == 10)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_98 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_98);
lean_dec_ref(x_72);
x_99 = l_Lean_IR_EmitC_argToCString___closed__0;
x_100 = l_Nat_reprFast(x_4);
x_101 = lean_string_append(x_99, x_100);
lean_dec_ref(x_100);
x_102 = lean_string_append(x_69, x_101);
lean_dec_ref(x_101);
x_103 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_104 = lean_string_append(x_102, x_103);
x_105 = lean_array_get_size(x_98);
lean_dec_ref(x_98);
x_106 = lean_nat_sub(x_3, x_105);
lean_dec(x_3);
x_107 = l_Nat_reprFast(x_106);
x_108 = lean_string_append(x_104, x_107);
lean_dec_ref(x_107);
x_109 = l_Lean_IR_EmitC_emitUProj___closed__0;
x_110 = lean_string_append(x_108, x_109);
x_111 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_112 = lean_box(0);
x_113 = lean_string_append(x_110, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_72);
x_115 = l_Lean_IR_EmitC_emitUProj___closed__3;
x_116 = lean_string_append(x_69, x_115);
x_117 = l_Lean_IR_EmitC_argToCString___closed__0;
x_118 = l_Nat_reprFast(x_4);
x_119 = lean_string_append(x_117, x_118);
lean_dec_ref(x_118);
x_120 = lean_string_append(x_116, x_119);
lean_dec_ref(x_119);
x_121 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_122 = lean_string_append(x_120, x_121);
x_123 = l_Nat_reprFast(x_3);
x_124 = lean_string_append(x_122, x_123);
lean_dec_ref(x_123);
x_125 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_126 = lean_string_append(x_124, x_125);
x_127 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_128 = lean_box(0);
x_129 = lean_string_append(x_126, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("));", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_get_float", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_get_float32", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_get_uint8", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_get_uint16", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_get_uint32", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_get_uint64", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_8);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_7, 5);
x_40 = lean_box(0);
x_41 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_40, x_39, x_6);
if (lean_obj_tag(x_41) == 11)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec_ref(x_41);
lean_free_object(x_35);
lean_dec(x_4);
x_42 = l_Lean_IR_EmitC_emitSSet___closed__0;
x_43 = lean_string_append(x_37, x_42);
x_44 = l_Lean_IR_EmitC_toCType(x_2, x_7, x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lean_IR_EmitC_argToCString___closed__0;
x_52 = l_Nat_reprFast(x_6);
x_53 = lean_string_append(x_51, x_52);
lean_dec_ref(x_52);
x_54 = lean_string_append(x_50, x_53);
lean_dec_ref(x_53);
x_55 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_Nat_reprFast(x_3);
x_58 = lean_string_append(x_56, x_57);
lean_dec_ref(x_57);
x_59 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_60 = lean_string_append(x_58, x_59);
x_61 = l_Nat_reprFast(x_5);
x_62 = lean_string_append(x_60, x_61);
lean_dec_ref(x_61);
x_63 = l_Lean_IR_EmitC_emitSProj___closed__0;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_66 = lean_string_append(x_64, x_65);
x_67 = lean_box(0);
lean_ctor_set(x_44, 1, x_66);
lean_ctor_set(x_44, 0, x_67);
return x_44;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_68 = lean_ctor_get(x_44, 0);
x_69 = lean_ctor_get(x_44, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_44);
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_72 = lean_string_append(x_70, x_71);
x_73 = l_Lean_IR_EmitC_argToCString___closed__0;
x_74 = l_Nat_reprFast(x_6);
x_75 = lean_string_append(x_73, x_74);
lean_dec_ref(x_74);
x_76 = lean_string_append(x_72, x_75);
lean_dec_ref(x_75);
x_77 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_78 = lean_string_append(x_76, x_77);
x_79 = l_Nat_reprFast(x_3);
x_80 = lean_string_append(x_78, x_79);
lean_dec_ref(x_79);
x_81 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Nat_reprFast(x_5);
x_84 = lean_string_append(x_82, x_83);
lean_dec_ref(x_83);
x_85 = l_Lean_IR_EmitC_emitSProj___closed__0;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_41) == 10)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_41);
lean_free_object(x_35);
lean_dec(x_4);
x_91 = l_Lean_IR_EmitC_emitSSet___closed__0;
x_92 = lean_string_append(x_37, x_91);
x_93 = l_Lean_IR_EmitC_toCType(x_2, x_7, x_92);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
x_97 = lean_string_append(x_96, x_95);
lean_dec(x_95);
x_98 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_99 = lean_string_append(x_97, x_98);
x_100 = l_Lean_IR_EmitC_argToCString___closed__0;
x_101 = l_Nat_reprFast(x_6);
x_102 = lean_string_append(x_100, x_101);
lean_dec_ref(x_101);
x_103 = lean_string_append(x_99, x_102);
lean_dec_ref(x_102);
x_104 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_105 = lean_string_append(x_103, x_104);
x_106 = l_Nat_reprFast(x_5);
x_107 = lean_string_append(x_105, x_106);
lean_dec_ref(x_106);
x_108 = l_Lean_IR_EmitC_emitSProj___closed__0;
x_109 = lean_string_append(x_107, x_108);
x_110 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_box(0);
lean_ctor_set(x_93, 1, x_111);
lean_ctor_set(x_93, 0, x_112);
return x_93;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_113 = lean_ctor_get(x_93, 0);
x_114 = lean_ctor_get(x_93, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_93);
x_115 = lean_string_append(x_114, x_113);
lean_dec(x_113);
x_116 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_117 = lean_string_append(x_115, x_116);
x_118 = l_Lean_IR_EmitC_argToCString___closed__0;
x_119 = l_Nat_reprFast(x_6);
x_120 = lean_string_append(x_118, x_119);
lean_dec_ref(x_119);
x_121 = lean_string_append(x_117, x_120);
lean_dec_ref(x_120);
x_122 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_123 = lean_string_append(x_121, x_122);
x_124 = l_Nat_reprFast(x_5);
x_125 = lean_string_append(x_123, x_124);
lean_dec_ref(x_124);
x_126 = l_Lean_IR_EmitC_emitSProj___closed__0;
x_127 = lean_string_append(x_125, x_126);
x_128 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_dec(x_41);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_132; lean_object* x_133; 
lean_free_object(x_35);
x_132 = l_Lean_IR_EmitC_emitSProj___closed__1;
x_133 = lean_string_append(x_37, x_132);
x_9 = x_133;
goto block_34;
}
case 9:
{
lean_object* x_134; lean_object* x_135; 
lean_free_object(x_35);
x_134 = l_Lean_IR_EmitC_emitSProj___closed__2;
x_135 = lean_string_append(x_37, x_134);
x_9 = x_135;
goto block_34;
}
case 1:
{
lean_object* x_136; lean_object* x_137; 
lean_free_object(x_35);
x_136 = l_Lean_IR_EmitC_emitSProj___closed__3;
x_137 = lean_string_append(x_37, x_136);
x_9 = x_137;
goto block_34;
}
case 2:
{
lean_object* x_138; lean_object* x_139; 
lean_free_object(x_35);
x_138 = l_Lean_IR_EmitC_emitSProj___closed__4;
x_139 = lean_string_append(x_37, x_138);
x_9 = x_139;
goto block_34;
}
case 3:
{
lean_object* x_140; lean_object* x_141; 
lean_free_object(x_35);
x_140 = l_Lean_IR_EmitC_emitSProj___closed__5;
x_141 = lean_string_append(x_37, x_140);
x_9 = x_141;
goto block_34;
}
case 4:
{
lean_object* x_142; lean_object* x_143; 
lean_free_object(x_35);
x_142 = l_Lean_IR_EmitC_emitSProj___closed__6;
x_143 = lean_string_append(x_37, x_142);
x_9 = x_143;
goto block_34;
}
default: 
{
lean_object* x_144; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_144 = l_Lean_IR_EmitC_emitSSet___closed__10;
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_144);
return x_35;
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_35, 1);
lean_inc(x_145);
lean_dec(x_35);
x_146 = lean_ctor_get(x_7, 5);
x_147 = lean_box(0);
x_148 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_emitInc_spec__0___redArg(x_147, x_146, x_6);
if (lean_obj_tag(x_148) == 11)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec_ref(x_148);
lean_dec(x_4);
x_149 = l_Lean_IR_EmitC_emitSSet___closed__0;
x_150 = lean_string_append(x_145, x_149);
x_151 = l_Lean_IR_EmitC_toCType(x_2, x_7, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_string_append(x_153, x_152);
lean_dec(x_152);
x_156 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_157 = lean_string_append(x_155, x_156);
x_158 = l_Lean_IR_EmitC_argToCString___closed__0;
x_159 = l_Nat_reprFast(x_6);
x_160 = lean_string_append(x_158, x_159);
lean_dec_ref(x_159);
x_161 = lean_string_append(x_157, x_160);
lean_dec_ref(x_160);
x_162 = l_Lean_IR_EmitC_emitUSet___closed__0;
x_163 = lean_string_append(x_161, x_162);
x_164 = l_Nat_reprFast(x_3);
x_165 = lean_string_append(x_163, x_164);
lean_dec_ref(x_164);
x_166 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_167 = lean_string_append(x_165, x_166);
x_168 = l_Nat_reprFast(x_5);
x_169 = lean_string_append(x_167, x_168);
lean_dec_ref(x_168);
x_170 = l_Lean_IR_EmitC_emitSProj___closed__0;
x_171 = lean_string_append(x_169, x_170);
x_172 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_154;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_148) == 10)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_148);
lean_dec(x_4);
x_176 = l_Lean_IR_EmitC_emitSSet___closed__0;
x_177 = lean_string_append(x_145, x_176);
x_178 = l_Lean_IR_EmitC_toCType(x_2, x_7, x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_string_append(x_180, x_179);
lean_dec(x_179);
x_183 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_184 = lean_string_append(x_182, x_183);
x_185 = l_Lean_IR_EmitC_argToCString___closed__0;
x_186 = l_Nat_reprFast(x_6);
x_187 = lean_string_append(x_185, x_186);
lean_dec_ref(x_186);
x_188 = lean_string_append(x_184, x_187);
lean_dec_ref(x_187);
x_189 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_190 = lean_string_append(x_188, x_189);
x_191 = l_Nat_reprFast(x_5);
x_192 = lean_string_append(x_190, x_191);
lean_dec_ref(x_191);
x_193 = l_Lean_IR_EmitC_emitSProj___closed__0;
x_194 = lean_string_append(x_192, x_193);
x_195 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_196 = lean_string_append(x_194, x_195);
x_197 = lean_box(0);
if (lean_is_scalar(x_181)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_181;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
else
{
lean_dec(x_148);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_199; lean_object* x_200; 
x_199 = l_Lean_IR_EmitC_emitSProj___closed__1;
x_200 = lean_string_append(x_145, x_199);
x_9 = x_200;
goto block_34;
}
case 9:
{
lean_object* x_201; lean_object* x_202; 
x_201 = l_Lean_IR_EmitC_emitSProj___closed__2;
x_202 = lean_string_append(x_145, x_201);
x_9 = x_202;
goto block_34;
}
case 1:
{
lean_object* x_203; lean_object* x_204; 
x_203 = l_Lean_IR_EmitC_emitSProj___closed__3;
x_204 = lean_string_append(x_145, x_203);
x_9 = x_204;
goto block_34;
}
case 2:
{
lean_object* x_205; lean_object* x_206; 
x_205 = l_Lean_IR_EmitC_emitSProj___closed__4;
x_206 = lean_string_append(x_145, x_205);
x_9 = x_206;
goto block_34;
}
case 3:
{
lean_object* x_207; lean_object* x_208; 
x_207 = l_Lean_IR_EmitC_emitSProj___closed__5;
x_208 = lean_string_append(x_145, x_207);
x_9 = x_208;
goto block_34;
}
case 4:
{
lean_object* x_209; lean_object* x_210; 
x_209 = l_Lean_IR_EmitC_emitSProj___closed__6;
x_210 = lean_string_append(x_145, x_209);
x_9 = x_210;
goto block_34;
}
default: 
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_211 = l_Lean_IR_EmitC_emitSSet___closed__10;
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_145);
return x_212;
}
}
}
}
}
block_34:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_EmitC_argToCString___closed__0;
x_13 = l_Nat_reprFast(x_6);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_11, x_14);
lean_dec_ref(x_14);
x_16 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_EmitC_emitOffset___redArg(x_4, x_5, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_23 = lean_string_append(x_20, x_22);
x_24 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_25 = lean_box(0);
x_26 = lean_string_append(x_23, x_24);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_31 = lean_box(0);
x_32 = lean_string_append(x_29, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_EmitC_emitSProj(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_IR_EmitC_toStringArgs_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_IR_EmitC_argToCString(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_IR_EmitC_argToCString(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_array_to_list(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___00Lean_IR_EmitC_toStringArgs_spec__0(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_10 = lean_box(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_23; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_nat_sub(x_4, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
lean_inc_ref(x_2);
x_28 = lean_array_get_borrowed(x_2, x_3, x_15);
x_29 = lean_ctor_get(x_28, 1);
x_30 = l_Lean_IR_IRType_isErased(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_IR_IRType_isVoid(x_29);
x_23 = x_31;
goto block_27;
}
else
{
x_23 = x_30;
goto block_27;
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_fget_borrowed(x_1, x_15);
lean_dec(x_15);
lean_inc(x_18);
x_19 = l_Lean_IR_EmitC_emitArg___redArg(x_18, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_5 = x_13;
x_6 = x_16;
x_7 = x_20;
goto _start;
}
block_27:
{
if (x_23 == 0)
{
if (x_6 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_25 = lean_string_append(x_7, x_24);
x_16 = x_23;
x_17 = x_25;
goto block_22;
}
else
{
x_16 = x_23;
x_17 = x_7;
goto block_22;
}
}
else
{
lean_dec(x_15);
x_5 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = l_Lean_IR_instInhabitedParam_default;
x_7 = lean_string_append(x_5, x_1);
x_8 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_array_get_size(x_3);
x_11 = 1;
x_12 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(x_3, x_6, x_2, x_10, x_10, x_11, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_17 = lean_string_append(x_14, x_16);
x_18 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(0);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSimpleExternalCall(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
x_11 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitExternCall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to emit extern application '", 35, 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_16; lean_object* x_17; 
x_16 = l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__1;
x_17 = l_Lean_getExternEntryFor(x_3, x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
switch (lean_obj_tag(x_18)) {
case 2:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_IR_EmitC_emitSimpleExternalCall(x_19, x_2, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_19);
return x_20;
}
case 1:
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = l_Lean_IR_EmitC_toStringArgs(x_4);
x_25 = l_Lean_expandExternPattern(x_22, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_6, x_25);
lean_dec_ref(x_25);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_30 = lean_box(0);
x_31 = lean_string_append(x_28, x_29);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_31);
lean_ctor_set(x_18, 0, x_30);
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = l_Lean_IR_EmitC_toStringArgs(x_4);
x_34 = l_Lean_expandExternPattern(x_32, x_33);
lean_dec(x_33);
x_35 = lean_string_append(x_6, x_34);
lean_dec_ref(x_34);
x_36 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_39 = lean_box(0);
x_40 = lean_string_append(x_37, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
default: 
{
lean_dec(x_18);
lean_dec_ref(x_4);
x_7 = x_6;
goto block_15;
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_4);
x_7 = x_6;
goto block_15;
}
block_15:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_IR_EmitC_emitExternCall___closed__0;
x_9 = 1;
x_10 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec_ref(x_10);
x_12 = l_Lean_IR_EmitC_getDecl___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitExternCall(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_5);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc_ref(x_4);
lean_inc(x_2);
x_24 = l_Lean_IR_EmitC_getDecl(x_2, x_4, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_25);
lean_inc_ref(x_4);
x_28 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_3);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_6 = x_29;
goto block_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_34 = lean_string_append(x_29, x_33);
x_35 = l_Lean_IR_EmitC_emitFullAppArgs(x_27, x_3, x_4, x_34);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_27);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_6 = x_38;
goto block_13;
}
else
{
return x_35;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_28;
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_25, 3);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_40) == 3)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 1);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec_ref(x_24);
x_43 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_43);
lean_dec_ref(x_25);
lean_inc_ref(x_4);
x_44 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_3);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_dec_ref(x_43);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = x_45;
goto block_21;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_50 = lean_string_append(x_45, x_49);
x_51 = l_Lean_IR_EmitC_emitFullAppArgs(x_43, x_3, x_4, x_50);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_43);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_54 = lean_string_append(x_52, x_53);
x_14 = x_54;
goto block_21;
}
else
{
return x_51;
}
}
}
else
{
lean_dec_ref(x_43);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_44;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc_ref(x_39);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_dec_ref(x_24);
x_56 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_56);
lean_dec_ref(x_25);
x_57 = l_Lean_IR_EmitC_emitExternCall(x_2, x_56, x_39, x_3, x_4, x_55);
lean_dec_ref(x_4);
lean_dec_ref(x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc_ref(x_39);
x_58 = lean_ctor_get(x_24, 1);
lean_inc(x_58);
lean_dec_ref(x_24);
x_59 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_59);
lean_dec_ref(x_25);
x_60 = l_Lean_IR_EmitC_emitExternCall(x_2, x_59, x_39, x_3, x_4, x_58);
lean_dec_ref(x_4);
lean_dec_ref(x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_inc(x_39);
x_61 = lean_ctor_get(x_24, 1);
lean_inc(x_61);
lean_dec_ref(x_24);
x_62 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_62);
lean_dec_ref(x_25);
x_63 = l_Lean_IR_EmitC_emitExternCall(x_2, x_62, x_39, x_3, x_4, x_61);
lean_dec_ref(x_4);
lean_dec_ref(x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_24);
if (x_64 == 0)
{
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_24, 0);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_24);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_10 = lean_box(0);
x_11 = lean_string_append(x_8, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_18 = lean_box(0);
x_19 = lean_string_append(x_16, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_closure_set(", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_14 = lean_nat_sub(x_5, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = lean_array_fget_borrowed(x_1, x_15);
x_17 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0;
x_18 = lean_string_append(x_7, x_17);
x_19 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_2);
x_20 = l_Nat_reprFast(x_2);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = lean_string_append(x_22, x_3);
x_24 = l_Nat_reprFast(x_15);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = lean_string_append(x_25, x_3);
lean_inc(x_16);
x_27 = l_Lean_IR_EmitC_emitArg___redArg(x_16, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_string_append(x_28, x_4);
x_30 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_31 = lean_string_append(x_29, x_30);
x_6 = x_13;
x_7 = x_31;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitPartialApp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_alloc_closure((void*)(", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitPartialApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("), ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_4);
lean_inc(x_2);
x_6 = l_Lean_IR_EmitC_getDecl(x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_1);
x_9 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitPartialApp___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_Decl_params(x_7);
lean_dec(x_7);
x_16 = lean_array_get_size(x_15);
lean_dec_ref(x_15);
x_17 = l_Lean_IR_EmitC_emitPartialApp___closed__1;
x_18 = lean_string_append(x_14, x_17);
x_19 = l_Nat_reprFast(x_16);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_array_get_size(x_3);
x_24 = l_Nat_reprFast(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_30 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(x_3, x_1, x_21, x_26, x_23, x_23, x_29);
return x_30;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_13;
}
}
else
{
uint8_t x_31; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
return x_6;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitPartialApp(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_apply_", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ lean_object* _aargs[] = {", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("};", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_apply_m(", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", _aargs); }", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_closureMaxArgs;
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_5);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitApp___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_7);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_EmitC_argToCString___closed__0;
x_18 = l_Nat_reprFast(x_2);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_16, x_19);
lean_dec_ref(x_19);
x_21 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_28 = lean_string_append(x_25, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_30 = lean_box(0);
x_31 = lean_string_append(x_28, x_29);
lean_ctor_set(x_23, 1, x_31);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_36 = lean_box(0);
x_37 = lean_string_append(x_34, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_39 = l_Lean_IR_EmitC_emitApp___closed__1;
x_40 = lean_string_append(x_5, x_39);
x_41 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_IR_EmitC_emitApp___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_46 = lean_string_append(x_44, x_45);
x_47 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_46);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = l_Lean_IR_EmitC_emitApp___closed__3;
x_52 = lean_string_append(x_49, x_51);
x_53 = l_Lean_IR_EmitC_argToCString___closed__0;
x_54 = l_Nat_reprFast(x_2);
x_55 = lean_string_append(x_53, x_54);
lean_dec_ref(x_54);
x_56 = lean_string_append(x_52, x_55);
lean_dec_ref(x_55);
x_57 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = l_Nat_reprFast(x_7);
x_60 = lean_string_append(x_58, x_59);
lean_dec_ref(x_59);
x_61 = l_Lean_IR_EmitC_emitApp___closed__4;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_box(0);
x_64 = lean_string_append(x_62, x_45);
lean_ctor_set(x_47, 1, x_64);
lean_ctor_set(x_47, 0, x_63);
return x_47;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_65 = lean_ctor_get(x_47, 1);
lean_inc(x_65);
lean_dec(x_47);
x_66 = l_Lean_IR_EmitC_emitApp___closed__3;
x_67 = lean_string_append(x_65, x_66);
x_68 = l_Lean_IR_EmitC_argToCString___closed__0;
x_69 = l_Nat_reprFast(x_2);
x_70 = lean_string_append(x_68, x_69);
lean_dec_ref(x_69);
x_71 = lean_string_append(x_67, x_70);
lean_dec_ref(x_70);
x_72 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_73 = lean_string_append(x_71, x_72);
x_74 = l_Nat_reprFast(x_7);
x_75 = lean_string_append(x_73, x_74);
lean_dec_ref(x_74);
x_76 = l_Lean_IR_EmitC_emitApp___closed__4;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_box(0);
x_79 = lean_string_append(x_77, x_45);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitApp(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box_usize", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box_uint32", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box_uint64", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box_float", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box_float32", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_IR_EmitC_emitBoxFn___closed__0;
x_6 = lean_box(0);
x_7 = lean_string_append(x_4, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_IR_EmitC_emitBoxFn___closed__1;
x_10 = lean_box(0);
x_11 = lean_string_append(x_4, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
case 4:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_IR_EmitC_emitBoxFn___closed__2;
x_14 = lean_box(0);
x_15 = lean_string_append(x_4, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_IR_EmitC_emitBoxFn___closed__3;
x_18 = lean_box(0);
x_19 = lean_string_append(x_4, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
case 9:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_IR_EmitC_emitBoxFn___closed__4;
x_22 = lean_box(0);
x_23 = lean_string_append(x_4, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
case 10:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_3, 6);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_26, x_25, x_1);
lean_dec_ref(x_1);
x_28 = l_Lean_IR_IRType_isStruct(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_IR_EmitC_structBoxFnPrefix___closed__0;
x_30 = lean_string_append(x_4, x_29);
x_31 = lean_box(0);
x_32 = l_Nat_reprFast(x_27);
x_33 = lean_string_append(x_30, x_32);
lean_dec_ref(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0;
x_36 = lean_string_append(x_4, x_35);
x_37 = l_Nat_reprFast(x_27);
x_38 = lean_string_append(x_36, x_37);
lean_dec_ref(x_37);
x_39 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_26, x_25, x_2);
x_42 = lean_box(0);
x_43 = l_Nat_reprFast(x_41);
x_44 = lean_string_append(x_40, x_43);
lean_dec_ref(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
case 11:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_3, 6);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_47, x_46, x_1);
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_1, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_52 = l_Lean_IR_IRType_isStruct(x_2);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_IR_EmitC_structBoxFnPrefix___closed__0;
x_54 = lean_string_append(x_4, x_53);
x_55 = lean_box(0);
x_56 = l_Nat_reprFast(x_48);
x_57 = lean_string_append(x_54, x_56);
lean_dec_ref(x_56);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_57);
lean_ctor_set(x_1, 0, x_55);
return x_1;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0;
x_59 = lean_string_append(x_4, x_58);
x_60 = l_Nat_reprFast(x_48);
x_61 = lean_string_append(x_59, x_60);
lean_dec_ref(x_60);
x_62 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0;
x_63 = lean_string_append(x_61, x_62);
x_64 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_47, x_46, x_2);
x_65 = lean_box(0);
x_66 = l_Nat_reprFast(x_64);
x_67 = lean_string_append(x_63, x_66);
lean_dec_ref(x_66);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set(x_1, 0, x_65);
return x_1;
}
}
else
{
uint8_t x_68; 
lean_dec(x_1);
x_68 = l_Lean_IR_IRType_isStruct(x_2);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = l_Lean_IR_EmitC_structBoxFnPrefix___closed__0;
x_70 = lean_string_append(x_4, x_69);
x_71 = lean_box(0);
x_72 = l_Nat_reprFast(x_48);
x_73 = lean_string_append(x_70, x_72);
lean_dec_ref(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0;
x_76 = lean_string_append(x_4, x_75);
x_77 = l_Nat_reprFast(x_48);
x_78 = lean_string_append(x_76, x_77);
lean_dec_ref(x_77);
x_79 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_47, x_46, x_2);
x_82 = lean_box(0);
x_83 = l_Nat_reprFast(x_81);
x_84 = lean_string_append(x_80, x_83);
lean_dec_ref(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
default: 
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_1);
x_86 = l_Lean_IR_EmitC_emitBoxFn___closed__5;
x_87 = lean_box(0);
x_88 = lean_string_append(x_4, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitBoxFn(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_IR_EmitC_emitBoxFn(x_3, x_4, x_5, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_14 = lean_string_append(x_11, x_13);
x_15 = l_Lean_IR_EmitC_argToCString___closed__0;
x_16 = l_Nat_reprFast(x_2);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = lean_string_append(x_14, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_22 = lean_box(0);
x_23 = lean_string_append(x_20, x_21);
lean_ctor_set(x_9, 1, x_23);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lean_IR_EmitC_argToCString___closed__0;
x_28 = l_Nat_reprFast(x_2);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = lean_string_append(x_26, x_29);
lean_dec_ref(x_29);
x_31 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_34 = lean_box(0);
x_35 = lean_string_append(x_32, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitBox(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnboxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isStruct(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_IR_getUnboxOpName(x_1);
x_6 = lean_box(0);
x_7 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 6);
x_10 = l_Lean_IR_EmitC_structUnboxFnPrefix___closed__0;
x_11 = lean_string_append(x_3, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0___redArg(x_12, x_9, x_1);
x_14 = lean_box(0);
x_15 = l_Nat_reprFast(x_13);
x_16 = lean_string_append(x_11, x_15);
lean_dec_ref(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnboxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitUnboxFn(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_IR_EmitC_emitUnboxFn(x_2, x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_13 = lean_string_append(x_10, x_12);
x_14 = l_Lean_IR_EmitC_argToCString___closed__0;
x_15 = l_Nat_reprFast(x_3);
x_16 = lean_string_append(x_14, x_15);
lean_dec_ref(x_15);
x_17 = lean_string_append(x_13, x_16);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_21 = lean_box(0);
x_22 = lean_string_append(x_19, x_20);
lean_ctor_set(x_8, 1, x_22);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_IR_EmitC_argToCString___closed__0;
x_27 = l_Nat_reprFast(x_3);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_33 = lean_box(0);
x_34 = lean_string_append(x_31, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUnbox(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIsShared___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("!lean_is_exclusive(", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = l_Lean_IR_EmitC_emitIsShared___redArg___closed__0;
x_9 = lean_string_append(x_6, x_8);
x_10 = l_Lean_IR_EmitC_argToCString___closed__0;
x_11 = l_Nat_reprFast(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_17 = lean_box(0);
x_18 = lean_string_append(x_15, x_16);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = l_Lean_IR_EmitC_emitIsShared___redArg___closed__0;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_IR_EmitC_argToCString___closed__0;
x_23 = l_Nat_reprFast(x_2);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = lean_string_append(x_21, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_29 = lean_box(0);
x_30 = lean_string_append(x_27, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitIsShared___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitIsShared(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_digitChar(x_1);
x_3 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1;
x_4 = lean_string_push(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toHexDigit(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\\?", 2, 2);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\\"", 2, 2);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\\\", 2, 2);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\t", 2, 2);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\r", 2, 2);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_next_fast(x_2, x_3);
x_10 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
x_11 = 10;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 13;
x_14 = lean_uint32_dec_eq(x_10, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 9;
x_16 = lean_uint32_dec_eq(x_10, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 92;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 34;
x_20 = lean_uint32_dec_eq(x_10, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 63;
x_22 = lean_uint32_dec_eq(x_10, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_uint32_to_nat(x_10);
x_24 = lean_unsigned_to_nat(31u);
x_25 = lean_nat_dec_le(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1;
x_27 = lean_string_push(x_26, x_10);
x_28 = lean_string_append(x_4, x_27);
lean_dec_ref(x_27);
x_3 = x_9;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0;
x_31 = lean_unsigned_to_nat(16u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_nat_shiftr(x_23, x_32);
x_34 = l_Lean_IR_EmitC_toHexDigit(x_33);
lean_dec(x_33);
x_35 = lean_string_append(x_30, x_34);
lean_dec_ref(x_34);
x_36 = lean_nat_mod(x_23, x_31);
lean_dec(x_23);
x_37 = l_Lean_IR_EmitC_toHexDigit(x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_35, x_37);
lean_dec_ref(x_37);
x_39 = lean_string_append(x_4, x_38);
lean_dec_ref(x_38);
x_3 = x_9;
x_4 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1;
x_42 = lean_string_append(x_4, x_41);
x_3 = x_9;
x_4 = x_42;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2;
x_45 = lean_string_append(x_4, x_44);
x_3 = x_9;
x_4 = x_45;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3;
x_48 = lean_string_append(x_4, x_47);
x_3 = x_9;
x_4 = x_48;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4;
x_51 = lean_string_append(x_4, x_50);
x_3 = x_9;
x_4 = x_51;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5;
x_54 = lean_string_append(x_4, x_53);
x_3 = x_9;
x_4 = x_54;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6;
x_57 = lean_string_append(x_4, x_56);
x_3 = x_9;
x_4 = x_57;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_IR_EmitC_quoteString___closed__0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_positions(x_5);
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(x_5, x_1, x_6, x_2);
lean_dec_ref(x_1);
lean_dec_ref(x_5);
x_8 = lean_string_append(x_7, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ULL", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("((size_t)", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ULL)", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_cstr_to_nat(\"", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\")", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_unsigned_to_nat(", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("u)", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isObj(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_cstr_to_nat("4294967296");
x_6 = lean_nat_dec_lt(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(5);
x_8 = l_Lean_IR_instBEqIRType_beq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Nat_reprFast(x_2);
x_10 = lean_string_append(x_3, x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitNumLit___redArg___closed__0;
x_12 = lean_box(0);
x_13 = lean_string_append(x_10, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = l_Lean_IR_EmitC_emitNumLit___redArg___closed__1;
x_16 = lean_string_append(x_3, x_15);
x_17 = l_Nat_reprFast(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_EmitC_emitNumLit___redArg___closed__2;
x_20 = lean_box(0);
x_21 = lean_string_append(x_18, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = l_Nat_reprFast(x_2);
x_25 = lean_string_append(x_3, x_24);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_1);
x_27 = lean_cstr_to_nat("4294967296");
x_28 = lean_nat_dec_lt(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = l_Lean_IR_EmitC_emitNumLit___redArg___closed__3;
x_30 = lean_string_append(x_3, x_29);
x_31 = l_Nat_reprFast(x_2);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = l_Lean_IR_EmitC_emitNumLit___redArg___closed__4;
x_34 = lean_box(0);
x_35 = lean_string_append(x_32, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = l_Lean_IR_EmitC_emitNumLit___redArg___closed__5;
x_38 = lean_string_append(x_3, x_37);
x_39 = l_Nat_reprFast(x_2);
x_40 = lean_string_append(x_38, x_39);
lean_dec_ref(x_39);
x_41 = l_Lean_IR_EmitC_emitNumLit___redArg___closed__6;
x_42 = lean_box(0);
x_43 = lean_string_append(x_40, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitNumLit___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitNumLit(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLit___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_mk_string_unchecked(", 25, 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = l_Lean_IR_EmitC_emitNumLit___redArg(x_2, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_13 = lean_string_append(x_10, x_12);
x_14 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_15 = lean_box(0);
x_16 = lean_string_append(x_13, x_14);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_21 = lean_box(0);
x_22 = lean_string_append(x_19, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_25 = lean_ctor_get(x_5, 1);
x_26 = lean_ctor_get(x_5, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_3);
x_28 = l_Lean_IR_EmitC_emitLit___redArg___closed__0;
x_29 = lean_string_append(x_25, x_28);
lean_inc_ref(x_27);
x_30 = l_Lean_IR_EmitC_quoteString(x_27);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_utf8_byte_size(x_27);
x_35 = l_Nat_reprFast(x_34);
x_36 = lean_string_append(x_33, x_35);
lean_dec_ref(x_35);
x_37 = lean_string_append(x_36, x_32);
x_38 = lean_string_length(x_27);
lean_dec_ref(x_27);
x_39 = l_Nat_reprFast(x_38);
x_40 = lean_string_append(x_37, x_39);
lean_dec_ref(x_39);
x_41 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_44 = lean_box(0);
x_45 = lean_string_append(x_42, x_43);
lean_ctor_set(x_5, 1, x_45);
lean_ctor_set(x_5, 0, x_44);
return x_5;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
lean_dec(x_5);
x_47 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_47);
lean_dec_ref(x_3);
x_48 = l_Lean_IR_EmitC_emitLit___redArg___closed__0;
x_49 = lean_string_append(x_46, x_48);
lean_inc_ref(x_47);
x_50 = l_Lean_IR_EmitC_quoteString(x_47);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_utf8_byte_size(x_47);
x_55 = l_Nat_reprFast(x_54);
x_56 = lean_string_append(x_53, x_55);
lean_dec_ref(x_55);
x_57 = lean_string_append(x_56, x_52);
x_58 = lean_string_length(x_47);
lean_dec_ref(x_47);
x_59 = l_Nat_reprFast(x_58);
x_60 = lean_string_append(x_57, x_59);
lean_dec_ref(x_59);
x_61 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_64 = lean_box(0);
x_65 = lean_string_append(x_62, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLit___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLit(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = l_Lean_IR_EmitC_emitCtor(x_1, x_2, x_6, x_7, x_4, x_5);
lean_dec_ref(x_7);
lean_dec(x_2);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = l_Lean_IR_EmitC_emitReset(x_1, x_9, x_10, x_4, x_5);
lean_dec_ref(x_4);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_15 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_3);
x_16 = l_Lean_IR_EmitC_emitReuse(x_1, x_12, x_13, x_14, x_15, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
lean_dec_ref(x_3);
x_20 = l_Lean_IR_EmitC_emitProj(x_1, x_17, x_18, x_19, x_4, x_5);
lean_dec_ref(x_4);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
lean_dec_ref(x_3);
x_24 = l_Lean_IR_EmitC_emitUProj(x_1, x_21, x_22, x_23, x_4, x_5);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 3);
lean_inc(x_28);
lean_dec_ref(x_3);
x_29 = l_Lean_IR_EmitC_emitSProj(x_1, x_2, x_25, x_26, x_27, x_28, x_4, x_5);
lean_dec_ref(x_4);
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_3);
x_32 = l_Lean_IR_EmitC_emitFullApp(x_1, x_30, x_31, x_4, x_5);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_3);
x_35 = l_Lean_IR_EmitC_emitPartialApp(x_1, x_33, x_34, x_4, x_5);
lean_dec_ref(x_34);
return x_35;
}
case 8:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_3);
x_38 = l_Lean_IR_EmitC_emitApp(x_1, x_36, x_37, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_37);
return x_38;
}
case 9:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_dec_ref(x_3);
x_41 = l_Lean_IR_EmitC_emitBox(x_1, x_40, x_39, x_2, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_41;
}
case 10:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
lean_dec_ref(x_3);
x_43 = l_Lean_IR_EmitC_emitUnbox(x_1, x_2, x_42, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_43;
}
case 11:
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_4);
x_44 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_44);
lean_dec_ref(x_3);
x_45 = l_Lean_IR_EmitC_emitLit___redArg(x_1, x_2, x_44, x_5);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_4);
lean_dec(x_2);
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec_ref(x_3);
x_47 = l_Lean_IR_EmitC_emitIsShared___redArg(x_1, x_46, x_5);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
if (lean_obj_tag(x_2) == 6)
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_name_eq(x_13, x_16);
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_box(x_17);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_5);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
uint8_t x_19; lean_object* x_20; 
x_19 = l_Lean_IR_instBEqVarId_beq(x_1, x_15);
x_20 = lean_box(x_19);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_5);
lean_ctor_set(x_2, 0, x_20);
return x_2;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_name_eq(x_21, x_23);
lean_dec(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_IR_instBEqVarId_beq(x_1, x_22);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
return x_29;
}
}
}
else
{
lean_dec_ref(x_2);
x_6 = x_5;
goto block_10;
}
}
else
{
lean_dec_ref(x_2);
x_6 = x_5;
goto block_10;
}
}
else
{
lean_dec_ref(x_2);
x_6 = x_5;
goto block_10;
}
block_10:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_isTailCall(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_instBEqVarId_beq(x_4, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_paramEqArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 1)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_2);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_nat_sub(x_5, x_6);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_10);
lean_inc(x_2);
x_12 = lean_array_get_borrowed(x_2, x_3, x_11);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_paramEqArg(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 1)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_nat_sub(x_5, x_6);
x_11 = lean_array_fget_borrowed(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_10, x_12);
lean_dec(x_10);
x_14 = lean_nat_sub(x_2, x_13);
lean_inc(x_14);
lean_inc(x_3);
x_15 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(x_13, x_3, x_4, x_11, x_14, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 1)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_nat_sub(x_5, x_6);
x_11 = lean_array_fget_borrowed(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_10, x_12);
lean_dec(x_10);
x_14 = lean_nat_sub(x_4, x_13);
lean_inc(x_14);
lean_inc(x_2);
x_15 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(x_13, x_2, x_3, x_11, x_14, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_nat_sub(x_6, x_12);
x_17 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(x_1, x_4, x_2, x_3, x_5, x_16);
return x_17;
}
else
{
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_IR_instInhabitedArg_default;
x_4 = lean_array_get_size(x_1);
x_5 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(x_1, x_3, x_2, x_4, x_4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_overwriteParam(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_IR_IRType_isVoid(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
else
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" _tmp_", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = lean_nat_sub(x_3, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = lean_array_fget_borrowed(x_1, x_14);
x_16 = l_Lean_IR_instInhabitedArg_default;
x_17 = lean_array_get_borrowed(x_16, x_2, x_14);
x_18 = l_Lean_IR_EmitC_paramEqArg(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = l_Lean_IR_EmitC_toCType(x_19, x_5, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_reprFast(x_14);
x_27 = lean_string_append(x_25, x_26);
lean_dec_ref(x_26);
x_28 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_29 = lean_string_append(x_27, x_28);
lean_inc(x_17);
x_30 = l_Lean_IR_EmitC_emitArg___redArg(x_17, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_35 = lean_string_append(x_33, x_34);
x_4 = x_12;
x_6 = x_35;
goto _start;
}
else
{
lean_dec(x_14);
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = _tmp_", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget_borrowed(x_1, x_13);
x_15 = l_Lean_IR_instInhabitedArg_default;
x_16 = lean_array_get_borrowed(x_15, x_2, x_13);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_18);
x_20 = l_Nat_reprFast(x_18);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_5, x_21);
lean_dec_ref(x_21);
x_23 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Nat_reprFast(x_13);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_30 = lean_string_append(x_28, x_29);
x_4 = x_11;
x_5 = x_30;
goto _start;
}
else
{
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget_borrowed(x_1, x_13);
x_15 = l_Lean_IR_instInhabitedArg_default;
x_16 = lean_array_get_borrowed(x_15, x_2, x_13);
lean_dec(x_13);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_18);
x_20 = l_Nat_reprFast(x_18);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_5, x_21);
lean_dec_ref(x_21);
x_23 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_24 = lean_string_append(x_22, x_23);
lean_inc(x_16);
x_25 = l_Lean_IR_EmitC_emitArg___redArg(x_16, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_30 = lean_string_append(x_28, x_29);
x_4 = x_11;
x_5 = x_30;
goto _start;
}
else
{
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goto _start;", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid tail call", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bug at emitTailCall", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_12; 
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_2, 4);
x_37 = lean_array_get_size(x_36);
x_38 = lean_array_get_size(x_34);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_34);
x_40 = l_Lean_IR_EmitC_emitTailCall___closed__1;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_free_object(x_1);
x_41 = l_Array_zip___redArg(x_36, x_34);
lean_dec_ref(x_34);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_get_size(x_41);
x_44 = l_Lean_IR_EmitC_emitTailCall___closed__2;
x_45 = lean_nat_dec_lt(x_42, x_43);
if (x_45 == 0)
{
lean_dec_ref(x_41);
x_12 = x_44;
goto block_32;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
if (x_45 == 0)
{
lean_dec_ref(x_41);
x_12 = x_44;
goto block_32;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_43);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(x_41, x_47, x_48, x_44);
lean_dec_ref(x_41);
x_12 = x_49;
goto block_32;
}
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_43);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(x_41, x_50, x_51, x_44);
lean_dec_ref(x_41);
x_12 = x_52;
goto block_32;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_ctor_get(x_2, 4);
x_55 = lean_array_get_size(x_54);
x_56 = lean_array_get_size(x_53);
x_57 = lean_nat_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_53);
x_58 = l_Lean_IR_EmitC_emitTailCall___closed__1;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = l_Array_zip___redArg(x_54, x_53);
lean_dec_ref(x_53);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_array_get_size(x_60);
x_63 = l_Lean_IR_EmitC_emitTailCall___closed__2;
x_64 = lean_nat_dec_lt(x_61, x_62);
if (x_64 == 0)
{
lean_dec_ref(x_60);
x_12 = x_63;
goto block_32;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_62, x_62);
if (x_65 == 0)
{
if (x_64 == 0)
{
lean_dec_ref(x_60);
x_12 = x_63;
goto block_32;
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_62);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(x_60, x_66, x_67, x_63);
lean_dec_ref(x_60);
x_12 = x_68;
goto block_32;
}
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_62);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(x_60, x_69, x_70, x_63);
lean_dec_ref(x_60);
x_12 = x_71;
goto block_32;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_1);
x_72 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_3);
return x_73;
}
block_11:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_IR_EmitC_emitTailCall___closed__0;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_8 = lean_box(0);
x_9 = lean_string_append(x_6, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
block_32:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Array_unzip___redArg(x_12);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_IR_EmitC_overwriteParam(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_get_size(x_14);
x_18 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(x_14, x_15, x_17, x_17, x_3);
lean_dec(x_15);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_4 = x_19;
goto block_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_IR_EmitC_emitSpreadValue___closed__0;
x_21 = lean_string_append(x_3, x_20);
x_22 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_array_get_size(x_14);
x_25 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(x_14, x_15, x_24, x_24, x_2, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(x_14, x_15, x_24, x_24, x_26);
lean_dec(x_15);
lean_dec(x_14);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_22);
x_4 = x_31;
goto block_11;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitTailCall(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" == ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("else", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCase___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("switch (", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") {", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("case ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitJPs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("default: ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0;
x_20 = lean_string_append(x_6, x_19);
x_21 = l_Nat_reprFast(x_18);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_IR_EmitC_emitJPs___closed__0;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_26 = lean_string_append(x_24, x_25);
lean_inc_ref(x_5);
x_27 = l_Lean_IR_EmitC_emitFnBody(x_17, x_5, x_26);
x_7 = x_27;
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec_ref(x_15);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1;
x_30 = lean_string_append(x_6, x_29);
x_31 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_32 = lean_string_append(x_30, x_31);
lean_inc_ref(x_5);
x_33 = l_Lean_IR_EmitC_emitFnBody(x_28, x_5, x_32);
x_7 = x_33;
goto block_13;
}
}
else
{
lean_object* x_34; 
lean_dec_ref(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
block_13:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; lean_object* x_17; 
x_17 = l_Lean_IR_EmitC_isIf(x_3);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_IR_EmitC_emitIf(x_1, x_2, x_20, x_21, x_22, x_4, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_24 = l_Lean_IR_EmitC_emitCase___closed__0;
x_25 = lean_string_append(x_5, x_24);
x_26 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_4, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_IR_EmitC_emitCase___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_IR_ensureHasDefault(x_3);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_32);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_4);
x_6 = x_31;
goto block_13;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_box(0);
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
if (x_35 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_4);
x_6 = x_31;
goto block_13;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_34);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(x_32, x_38, x_39, x_36, x_4, x_31);
lean_dec_ref(x_32);
x_14 = x_40;
goto block_16;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_34);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(x_32, x_41, x_42, x_36, x_4, x_31);
lean_dec_ref(x_32);
x_14 = x_43;
goto block_16;
}
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_26;
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_10 = lean_box(0);
x_11 = lean_string_append(x_8, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_16:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_6 = x_15;
goto block_13;
}
else
{
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBlock___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("return ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBlock___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_internal_panic_unreachable();", 34, 34);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_IR_isTailCallTo(x_8, x_1);
lean_dec_ref(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc_ref(x_2);
x_10 = l_Lean_IR_EmitC_emitVDecl(x_4, x_5, x_6, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_1 = x_7;
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_2);
return x_10;
}
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_13 = l_Lean_IR_EmitC_emitTailCall(x_6, x_2, x_3);
lean_dec_ref(x_2);
return x_13;
}
}
case 1:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec_ref(x_1);
x_1 = x_14;
goto _start;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = l_Lean_IR_EmitC_emitSet___redArg(x_16, x_17, x_18, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_1 = x_19;
x_3 = x_21;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec_ref(x_2);
return x_20;
}
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = l_Lean_IR_EmitC_emitSetTag___redArg(x_23, x_24, x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_1 = x_25;
x_3 = x_27;
goto _start;
}
else
{
lean_dec(x_25);
lean_dec_ref(x_2);
return x_26;
}
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 4);
lean_inc(x_33);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_34 = l_Lean_IR_EmitC_emitUSet(x_29, x_30, x_31, x_32, x_2, x_3);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_1 = x_33;
x_3 = x_35;
goto _start;
}
else
{
lean_dec(x_33);
lean_dec_ref(x_2);
return x_34;
}
}
case 5:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 5);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 6);
lean_inc(x_43);
lean_dec_ref(x_1);
x_44 = l_Lean_IR_EmitC_emitSSet(x_37, x_38, x_39, x_40, x_41, x_42, x_2, x_3);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_1 = x_43;
x_3 = x_45;
goto _start;
}
else
{
lean_dec(x_43);
lean_dec_ref(x_2);
return x_44;
}
}
case 6:
{
uint8_t x_47; 
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
lean_dec_ref(x_1);
x_52 = l_Lean_IR_EmitC_emitInc(x_48, x_49, x_50, x_2, x_3);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
x_1 = x_51;
x_3 = x_53;
goto _start;
}
else
{
lean_dec(x_51);
lean_dec_ref(x_2);
return x_52;
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 2);
lean_inc(x_55);
lean_dec_ref(x_1);
x_1 = x_55;
goto _start;
}
}
case 7:
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_61 = lean_ctor_get(x_1, 2);
lean_inc(x_61);
lean_dec_ref(x_1);
x_62 = l_Lean_IR_EmitC_emitDec(x_58, x_59, x_60, x_2, x_3);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
x_1 = x_61;
x_3 = x_63;
goto _start;
}
else
{
lean_dec(x_61);
lean_dec_ref(x_2);
return x_62;
}
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_1, 2);
lean_inc(x_65);
lean_dec_ref(x_1);
x_1 = x_65;
goto _start;
}
}
case 8:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_dec_ref(x_1);
x_69 = l_Lean_IR_EmitC_emitDel___redArg(x_67, x_3);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_1 = x_68;
x_3 = x_70;
goto _start;
}
else
{
lean_dec(x_68);
lean_dec_ref(x_2);
return x_69;
}
}
case 9:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_74);
lean_dec_ref(x_1);
x_75 = l_Lean_IR_EmitC_emitCase(x_72, x_73, x_74, x_2, x_3);
lean_dec(x_73);
return x_75;
}
case 10:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_2);
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
lean_dec_ref(x_1);
x_77 = l_Lean_IR_EmitC_emitBlock___closed__0;
x_78 = lean_string_append(x_3, x_77);
x_79 = l_Lean_IR_EmitC_emitArg___redArg(x_76, x_78);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_79, 1);
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
x_83 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_84 = lean_string_append(x_81, x_83);
x_85 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_86 = lean_box(0);
x_87 = lean_string_append(x_84, x_85);
lean_ctor_set(x_79, 1, x_87);
lean_ctor_set(x_79, 0, x_86);
return x_79;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec(x_79);
x_89 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_90 = lean_string_append(x_88, x_89);
x_91 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_92 = lean_box(0);
x_93 = lean_string_append(x_90, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
return x_79;
}
}
case 11:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_96);
lean_dec_ref(x_1);
x_97 = l_Lean_IR_EmitC_emitJmp(x_95, x_96, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_96);
return x_97;
}
default: 
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_2);
x_98 = l_Lean_IR_EmitC_emitBlock___closed__1;
x_99 = lean_string_append(x_3, x_98);
x_100 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_101 = lean_box(0);
x_102 = lean_string_append(x_99, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJPs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_8 = l_Nat_reprFast(x_4);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_string_append(x_3, x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitJPs___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_14 = lean_string_append(x_12, x_13);
lean_inc_ref(x_2);
x_15 = l_Lean_IR_EmitC_emitFnBody(x_5, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_1 = x_6;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
else
{
uint8_t x_18; 
x_18 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_25 = l_Lean_IR_EmitC_emitSpreadValue___closed__0;
x_26 = lean_string_append(x_3, x_25);
x_27 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_28 = lean_string_append(x_26, x_27);
x_29 = 0;
lean_inc(x_1);
x_30 = l_Lean_IR_EmitC_declareVars(x_1, x_29, x_2, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec_ref(x_30);
x_4 = x_2;
x_5 = x_33;
goto block_24;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec_ref(x_30);
x_35 = lean_string_append(x_34, x_27);
x_4 = x_2;
x_5 = x_35;
goto block_24;
}
}
else
{
uint8_t x_36; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
block_24:
{
lean_object* x_6; 
lean_inc_ref(x_4);
lean_inc(x_1);
x_6 = l_Lean_IR_EmitC_emitBlock(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_IR_EmitC_emitJPs(x_1, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_13 = lean_string_append(x_10, x_12);
x_14 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_15 = lean_box(0);
x_16 = lean_string_append(x_13, x_14);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_21 = lean_box(0);
x_22 = lean_string_append(x_19, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
return x_8;
}
}
else
{
lean_dec_ref(x_4);
lean_dec(x_1);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_IR_EmitC_emitIf___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_IR_EmitC_emitIf___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_reprFast(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_19 = lean_string_append(x_17, x_18);
lean_inc_ref(x_6);
x_20 = l_Lean_IR_EmitC_emitFnBody(x_4, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_IR_EmitC_emitIf___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_18);
x_25 = l_Lean_IR_EmitC_emitFnBody(x_5, x_6, x_24);
return x_25;
}
else
{
lean_dec_ref(x_6);
lean_dec(x_5);
return x_20;
}
}
else
{
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitIf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitCase(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" c", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget_borrowed(x_2, x_4);
lean_inc(x_10);
x_11 = l_Lean_IR_EmitC_toCType(x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg___closed__0;
x_16 = lean_string_append(x_14, x_15);
lean_inc(x_4);
x_17 = l_Nat_reprFast(x_4);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
{
lean_object* _tmp_3 = x_24;
lean_object* _tmp_4 = x_3;
lean_object* _tmp_6 = x_22;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" i", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_4, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_array_fget_borrowed(x_2, x_4);
switch (lean_obj_tag(x_16)) {
case 6:
{
x_8 = x_3;
x_9 = x_7;
goto block_13;
}
case 13:
{
x_8 = x_3;
x_9 = x_7;
goto block_13;
}
default: 
{
lean_object* x_17; 
lean_inc(x_16);
x_17 = l_Lean_IR_EmitC_toCType(x_16, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg___closed__0;
x_22 = lean_string_append(x_20, x_21);
lean_inc(x_4);
x_23 = l_Nat_reprFast(x_4);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_28 = lean_string_append(x_26, x_27);
x_8 = x_3;
x_9 = x_28;
goto block_13;
}
else
{
uint8_t x_29; 
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" {", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("union {", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.EmitC.emitStructDefn", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: tys.size ≤ 256\n    ", 42, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitStructDefn___closed__3;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(894u);
x_4 = l_Lean_IR_EmitC_emitStructDefn___closed__2;
x_5 = l_Lean_IR_EmitC_emitUSet___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("} cs;", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uint8_t tag;", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("size_t u[", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uint8_t s[", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructDefn___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitUSet___closed__5;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(907u);
x_4 = l_Lean_IR_EmitC_emitStructDefn___closed__2;
x_5 = l_Lean_IR_EmitC_emitUSet___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructDefn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lean_IR_EmitC_emitStructDefn___closed__0;
x_14 = lean_string_append(x_2, x_13);
x_15 = lean_string_append(x_4, x_14);
lean_dec_ref(x_14);
x_16 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_17 = lean_string_append(x_15, x_16);
switch (lean_obj_tag(x_1)) {
case 11:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_array_get_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_IR_EmitC_emitStructDefn___closed__1;
x_22 = lean_string_append(x_17, x_21);
x_23 = lean_string_append(x_22, x_16);
x_24 = lean_box(0);
x_25 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg(x_19, x_18, x_24, x_20, x_24, x_3, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_unsigned_to_nat(256u);
x_28 = lean_nat_dec_le(x_19, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_29 = l_Lean_IR_EmitC_emitStructDefn___closed__4;
x_30 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_29, x_3, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_3);
x_31 = l_Lean_IR_EmitC_emitStructDefn___closed__5;
x_32 = lean_string_append(x_26, x_31);
x_33 = lean_string_append(x_32, x_16);
x_34 = l_Lean_IR_EmitC_optionLike_x3f(x_1);
lean_dec_ref(x_1);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lean_IR_EmitC_emitStructDefn___closed__6;
x_36 = lean_string_append(x_33, x_35);
x_37 = lean_string_append(x_36, x_16);
x_5 = x_37;
goto block_12;
}
else
{
lean_dec_ref(x_34);
x_5 = x_33;
goto block_12;
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_25;
}
}
case 10:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 3);
lean_inc(x_40);
lean_dec_ref(x_1);
x_41 = lean_array_get_size(x_38);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_box(0);
x_44 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg(x_41, x_38, x_43, x_42, x_43, x_3, x_17);
lean_dec_ref(x_3);
lean_dec_ref(x_38);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_60; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_60 = lean_nat_dec_eq(x_39, x_42);
if (x_60 == 0)
{
goto block_59;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_eq(x_40, x_42);
if (x_61 == 0)
{
goto block_59;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
x_5 = x_45;
goto block_12;
}
}
block_59:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = l_Lean_IR_EmitC_emitStructDefn___closed__7;
x_47 = l_Nat_reprFast(x_39);
x_48 = lean_string_append(x_46, x_47);
lean_dec_ref(x_47);
x_49 = l_Lean_IR_EmitC_emitUProj___closed__0;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_string_append(x_45, x_50);
lean_dec_ref(x_50);
x_52 = lean_string_append(x_51, x_16);
x_53 = l_Lean_IR_EmitC_emitStructDefn___closed__8;
x_54 = l_Nat_reprFast(x_40);
x_55 = lean_string_append(x_53, x_54);
lean_dec_ref(x_54);
x_56 = lean_string_append(x_55, x_49);
x_57 = lean_string_append(x_52, x_56);
lean_dec_ref(x_56);
x_58 = lean_string_append(x_57, x_16);
x_5 = x_58;
goto block_12;
}
}
else
{
lean_dec(x_40);
lean_dec(x_39);
return x_44;
}
}
default: 
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_62 = l_Lean_IR_EmitC_emitStructDefn___closed__9;
x_63 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_62, x_3, x_17);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_5 = x_64;
goto block_12;
}
else
{
return x_63;
}
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_IR_EmitC_emitApp___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_9 = lean_box(0);
x_10 = lean_string_append(x_7, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("break;", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0;
x_11 = lean_string_append(x_7, x_10);
lean_inc(x_4);
x_12 = l_Nat_reprFast(x_4);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_IR_EmitC_emitJPs___closed__0;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_17 = lean_string_append(x_15, x_16);
lean_inc_ref(x_2);
lean_inc_ref(x_6);
lean_inc(x_4);
x_18 = lean_apply_4(x_2, x_4, lean_box(0), x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___closed__0;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_16);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
{
lean_object* _tmp_3 = x_24;
lean_object* _tmp_4 = x_3;
lean_object* _tmp_6 = x_22;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUnionSwitch___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" == 0) {", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_IR_EmitC_emitCase___closed__0;
x_12 = lean_string_append(x_5, x_11);
x_13 = lean_string_append(x_12, x_2);
x_14 = l_Lean_IR_EmitC_emitCase___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg(x_1, x_3, x_18, x_10, x_18, x_4, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_24 = lean_string_append(x_21, x_23);
x_25 = lean_string_append(x_24, x_16);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_16);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
return x_19;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = l_Lean_IR_EmitC_emitIf___closed__0;
x_32 = lean_string_append(x_5, x_31);
x_33 = lean_string_append(x_32, x_2);
x_34 = l_Lean_IR_EmitC_emitUnionSwitch___closed__0;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_3);
lean_inc_ref(x_4);
x_39 = lean_apply_4(x_3, x_38, lean_box(0), x_4, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_string_append(x_42, x_36);
x_44 = lean_apply_4(x_3, x_6, lean_box(0), x_4, x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_49 = lean_string_append(x_46, x_48);
x_50 = lean_box(0);
x_51 = lean_string_append(x_49, x_36);
lean_ctor_set(x_44, 1, x_51);
lean_ctor_set(x_44, 0, x_50);
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_box(0);
x_56 = lean_string_append(x_54, x_36);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
return x_44;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_39;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_apply_4(x_3, x_58, lean_box(0), x_4, x_5);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUnionSwitch(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
lean_inc(x_12);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_12);
x_6 = x_15;
goto block_10;
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_array_uget(x_3, x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0;
x_13 = lean_string_append(x_8, x_12);
lean_inc(x_11);
x_14 = l_Nat_reprFast(x_11);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = l_Lean_IR_EmitC_emitJPs___closed__0;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_19 = lean_string_append(x_17, x_18);
lean_inc_ref(x_1);
lean_inc_ref(x_7);
x_20 = lean_apply_4(x_1, x_11, lean_box(0), x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_18);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
{
size_t _tmp_4 = x_26;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_7 = x_24;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec_ref(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_7 = l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__0;
x_8 = l_Array_ofFn___redArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_69 = lean_array_get_size(x_8);
x_70 = l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__1;
x_71 = lean_nat_dec_lt(x_9, x_69);
if (x_71 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_10 = x_70;
goto block_68;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_69, x_69);
if (x_72 == 0)
{
if (x_71 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_10 = x_70;
goto block_68;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_69);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__1(x_3, x_8, x_73, x_74, x_70);
lean_dec_ref(x_8);
x_10 = x_75;
goto block_68;
}
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_69);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__1(x_3, x_8, x_76, x_77, x_70);
lean_dec_ref(x_8);
x_10 = x_78;
goto block_68;
}
}
block_68:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_dec_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_16 = l_Lean_IR_EmitC_emitCase___closed__0;
x_17 = lean_string_append(x_6, x_16);
x_18 = lean_string_append(x_17, x_2);
x_19 = l_Lean_IR_EmitC_emitCase___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(0);
x_24 = lean_array_size(x_10);
x_25 = 0;
x_26 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitUnionSwitchWithImpossible_spec__0(x_4, x_23, x_10, x_24, x_25, x_23, x_5, x_22);
lean_dec_ref(x_10);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_31 = lean_string_append(x_28, x_30);
x_32 = lean_string_append(x_31, x_21);
lean_ctor_set(x_26, 1, x_32);
lean_ctor_set(x_26, 0, x_23);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_21);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
return x_26;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = l_Lean_IR_EmitC_emitIf___closed__0;
x_39 = lean_string_append(x_6, x_38);
x_40 = lean_string_append(x_39, x_2);
x_41 = l_Lean_IR_EmitC_emitUnionSwitch___closed__0;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_array_fget_borrowed(x_10, x_9);
lean_inc_ref(x_4);
lean_inc_ref(x_5);
lean_inc(x_45);
x_46 = lean_apply_4(x_4, x_45, lean_box(0), x_5, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_43);
x_51 = lean_array_fget(x_10, x_12);
lean_dec_ref(x_10);
x_52 = lean_apply_4(x_4, x_51, lean_box(0), x_5, x_50);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_57 = lean_string_append(x_54, x_56);
x_58 = lean_box(0);
x_59 = lean_string_append(x_57, x_43);
lean_ctor_set(x_52, 1, x_59);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_dec(x_52);
x_61 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_box(0);
x_64 = lean_string_append(x_62, x_43);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
return x_52;
}
}
else
{
lean_dec_ref(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_46;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_array_fget(x_10, x_9);
lean_dec_ref(x_10);
x_67 = lean_apply_4(x_4, x_66, lean_box(0), x_5, x_6);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitUnionSwitchWithImpossible(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 13:
{
goto block_9;
}
case 6:
{
goto block_9;
}
default: 
{
uint8_t x_10; 
x_10 = l_Lean_IR_IRType_isScalar(x_4);
if (x_10 == 0)
{
if (x_1 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_IR_EmitC_emitDecOfType(x_3, x_4, x_11, x_2, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___closed__0;
x_15 = l_Lean_IR_EmitC_emitIncOfType(x_3, x_4, x_13, x_2, x_14, x_5, x_6);
return x_15;
}
}
else
{
goto block_9;
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_2);
x_9 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__0(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x.cs.c", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___closed__0;
lean_inc(x_3);
x_8 = l_Nat_reprFast(x_3);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_array_fget_borrowed(x_1, x_3);
lean_dec(x_3);
lean_inc(x_10);
x_11 = lean_apply_4(x_2, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x.i", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_15; uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_6, x_1);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_array_fget_borrowed(x_2, x_6);
switch (lean_obj_tag(x_20)) {
case 13:
{
x_10 = x_9;
goto block_14;
}
case 6:
{
x_10 = x_9;
goto block_14;
}
default: 
{
uint8_t x_21; 
x_21 = l_Lean_IR_IRType_isScalar(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___closed__0;
lean_inc(x_6);
x_23 = l_Nat_reprFast(x_6);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
if (x_4 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Lean_IR_EmitC_emitDecOfType(x_24, x_20, x_25, x_5, x_8, x_9);
lean_dec_ref(x_24);
x_15 = x_26;
goto block_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___closed__0;
x_29 = l_Lean_IR_EmitC_emitIncOfType(x_24, x_20, x_27, x_5, x_28, x_8, x_9);
lean_dec_ref(x_24);
x_15 = x_29;
goto block_17;
}
}
else
{
x_10 = x_9;
goto block_14;
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
{
lean_object* _tmp_5 = x_12;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_8 = x_10;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_9 = _tmp_8;
}
goto _start;
}
block_17:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_10 = x_16;
goto block_14;
}
else
{
lean_dec(x_6);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_4);
x_11 = lean_unbox(x_5);
x_12 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_15; uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_6, x_1);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_array_fget_borrowed(x_2, x_6);
switch (lean_obj_tag(x_20)) {
case 13:
{
x_10 = x_9;
goto block_14;
}
case 6:
{
x_10 = x_9;
goto block_14;
}
default: 
{
uint8_t x_21; 
x_21 = l_Lean_IR_IRType_isScalar(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___closed__0;
lean_inc(x_6);
x_23 = l_Nat_reprFast(x_6);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
if (x_3 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Lean_IR_EmitC_emitDecOfType(x_24, x_20, x_25, x_4, x_8, x_9);
lean_dec_ref(x_24);
x_15 = x_26;
goto block_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___closed__0;
x_29 = l_Lean_IR_EmitC_emitIncOfType(x_24, x_20, x_27, x_4, x_28, x_8, x_9);
lean_dec_ref(x_24);
x_15 = x_29;
goto block_17;
}
}
else
{
x_10 = x_9;
goto block_14;
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_13 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg(x_1, x_2, x_5, x_3, x_4, x_12, x_5, x_8, x_10);
return x_13;
}
block_17:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_10 = x_16;
goto block_14;
}
else
{
lean_dec(x_6);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (x", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" != 0) {", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x.cs.c1", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x.tag", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static void ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" x) {", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" x, size_t n) {", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_52; 
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_box(x_3);
x_17 = lean_box(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___boxed), 6, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
if (x_3 == 0)
{
lean_object* x_71; 
x_71 = l_Lean_IR_EmitC_structDecFnPrefix___closed__0;
x_52 = x_71;
goto block_70;
}
else
{
lean_object* x_72; 
x_72 = l_Lean_IR_EmitC_structIncFnPrefix___closed__0;
x_52 = x_72;
goto block_70;
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_10 = lean_box(0);
x_11 = lean_string_append(x_8, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_51:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_IR_EmitC_optionLike_x3f(x_1);
lean_dec_ref(x_1);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__0;
x_25 = lean_string_append(x_20, x_24);
x_26 = l_Lean_IR_EmitC_emitPath(x_23, x_19, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__2;
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_array_get(x_14, x_21, x_33);
lean_dec_ref(x_21);
x_35 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__0(x_3, x_15, x_32, x_34, x_19, x_31);
lean_dec_ref(x_19);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_30);
x_6 = x_39;
goto block_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_22);
lean_inc_ref(x_21);
x_40 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___boxed), 6, 2);
lean_closure_set(x_40, 0, x_21);
lean_closure_set(x_40, 1, x_18);
x_41 = lean_array_get_size(x_21);
lean_dec_ref(x_21);
x_42 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__3;
x_43 = l_Lean_IR_EmitC_emitUnionSwitch(x_41, x_42, x_40, x_19, x_20);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_6 = x_44;
goto block_13;
}
else
{
return x_43;
}
}
}
else
{
lean_dec_ref(x_18);
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_1);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_box(0);
x_49 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___redArg(x_46, x_45, x_3, x_15, x_48, x_47, x_48, x_19, x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec_ref(x_49);
x_6 = x_50;
goto block_13;
}
else
{
return x_49;
}
}
else
{
lean_dec_ref(x_19);
lean_dec(x_1);
x_6 = x_20;
goto block_13;
}
}
}
block_70:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__4;
x_54 = lean_string_append(x_5, x_53);
x_55 = lean_string_append(x_54, x_52);
lean_dec_ref(x_52);
lean_inc(x_2);
x_56 = l_Nat_reprFast(x_2);
x_57 = lean_string_append(x_55, x_56);
lean_dec_ref(x_56);
x_58 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lean_IR_EmitC_structType(x_2);
x_61 = lean_string_append(x_59, x_60);
lean_dec_ref(x_60);
if (x_3 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__5;
x_63 = lean_string_append(x_61, x_62);
x_64 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_65 = lean_string_append(x_63, x_64);
x_19 = x_4;
x_20 = x_65;
goto block_51;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__6;
x_67 = lean_string_append(x_61, x_66);
x_68 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_69 = lean_string_append(x_67, x_68);
x_19 = x_4;
x_20 = x_69;
goto block_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructIncDecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitStructIncDecFn(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_4);
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_5);
x_15 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReshapeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_isObj(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitBoxFn(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_IR_EmitC_emitUnboxFn(x_2, x_3, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReshapeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitReshapeFn(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_compatibleReshape(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 10:
{
switch (lean_obj_tag(x_2)) {
case 10:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_array_get_size(x_12);
x_15 = lean_array_get_size(x_13);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___redArg(x_12, x_13, x_14);
return x_17;
}
}
case 11:
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
default: 
{
goto block_11;
}
}
}
case 11:
{
if (lean_obj_tag(x_2) == 10)
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
else
{
goto block_11;
}
}
default: 
{
goto block_11;
}
}
block_7:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_isStruct(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_isScalar(x_2);
if (x_5 == 0)
{
return x_3;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
block_11:
{
uint8_t x_8; 
x_8 = l_Lean_IR_IRType_isScalar(x_1);
if (x_8 == 0)
{
goto block_7;
}
else
{
uint8_t x_9; 
x_9 = l_Lean_IR_IRType_isStruct(x_2);
if (x_9 == 0)
{
goto block_7;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = l_Lean_IR_EmitC_compatibleReshape(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_compatibleReshape___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_compatibleReshape(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00Lean_IR_EmitC_compatibleReshape_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y.cs.c", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(x.cs.c", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__0;
x_10 = lean_string_append(x_8, x_9);
lean_inc(x_6);
x_11 = l_Nat_reprFast(x_6);
x_12 = lean_string_append(x_10, x_11);
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_14 = lean_string_append(x_12, x_13);
lean_inc(x_1);
x_15 = lean_array_get_borrowed(x_1, x_2, x_6);
x_16 = lean_array_get_borrowed(x_1, x_3, x_6);
lean_dec(x_6);
x_17 = l_Lean_IR_IRType_compatibleWith(x_15, x_16, x_4);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_inc(x_15);
x_18 = l_Lean_IR_EmitC_emitReshapeFn(x_15, x_16, x_7, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__1;
x_23 = lean_string_append(x_20, x_22);
x_24 = lean_string_append(x_23, x_11);
lean_dec_ref(x_11);
x_25 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_string_append(x_26, x_5);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_11);
lean_dec_ref(x_11);
x_33 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_box(0);
x_36 = lean_string_append(x_34, x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___closed__0;
x_39 = lean_string_append(x_14, x_38);
x_40 = lean_string_append(x_39, x_11);
lean_dec_ref(x_11);
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_box(0);
x_44 = lean_string_append(x_42, x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_IR_EmitC_emitStructReshapeFn___lam__0(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_emitStructReshapeFn___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = lean_array_get_borrowed(x_1, x_2, x_4);
x_6 = lean_array_get_borrowed(x_1, x_3, x_4);
x_7 = l_Lean_IR_EmitC_compatibleReshape(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_EmitC_emitStructReshapeFn___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_dec(x.i", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0___closed__0;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_1);
x_10 = lean_string_append(x_9, x_2);
x_11 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y.i", 3, 3);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(x.i", 4, 4);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("1", 1, 1);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = x.i", 6, 6);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = lean_box(0);", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_33; uint8_t x_34; lean_object* x_74; uint8_t x_75; uint8_t x_85; uint8_t x_88; 
x_88 = lean_nat_dec_lt(x_8, x_6);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_8);
lean_dec(x_2);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_9);
lean_ctor_set(x_89, 1, x_11);
return x_89;
}
else
{
lean_object* x_90; 
lean_inc(x_2);
x_90 = lean_array_get_borrowed(x_2, x_3, x_8);
switch (lean_obj_tag(x_90)) {
case 6:
{
x_85 = x_5;
goto block_87;
}
case 13:
{
x_85 = x_5;
goto block_87;
}
default: 
{
x_85 = x_7;
goto block_87;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_8, x_14);
lean_dec(x_8);
x_8 = x_15;
x_9 = x_12;
x_11 = x_13;
goto _start;
}
block_32:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec_ref(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec_ref(x_19);
x_12 = x_27;
x_13 = x_26;
goto block_17;
}
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
block_73:
{
lean_object* x_35; uint8_t x_36; 
lean_inc(x_2);
x_35 = lean_array_get_borrowed(x_2, x_3, x_8);
x_36 = l_Lean_IR_IRType_compatibleWith(x_33, x_35, x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0;
x_38 = lean_string_append(x_11, x_37);
lean_inc(x_8);
x_39 = l_Nat_reprFast(x_8);
x_40 = lean_string_append(x_38, x_39);
x_41 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_42 = lean_string_append(x_40, x_41);
lean_inc(x_33);
x_43 = l_Lean_IR_EmitC_emitReshapeFn(x_33, x_35, x_10, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_string_append(x_46, x_39);
x_48 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_IR_IRType_isObj(x_33);
lean_dec(x_33);
if (x_52 == 0)
{
lean_dec_ref(x_39);
x_12 = x_4;
x_13 = x_51;
goto block_17;
}
else
{
uint8_t x_53; 
x_53 = l_Lean_IR_EmitC_needsRC(x_35);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0(x_39, x_48, x_4, x_4, x_10, x_51);
lean_dec_ref(x_39);
x_18 = x_54;
goto block_32;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_string_append(x_37, x_39);
x_56 = lean_unsigned_to_nat(1u);
x_57 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__2;
x_58 = l_Lean_IR_EmitC_emitIncOfType(x_55, x_35, x_56, x_5, x_57, x_10, x_51);
lean_dec_ref(x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0(x_39, x_48, x_4, x_59, x_10, x_60);
lean_dec_ref(x_39);
x_18 = x_61;
goto block_32;
}
else
{
lean_dec_ref(x_39);
lean_dec(x_8);
lean_dec(x_2);
return x_58;
}
}
}
}
else
{
lean_dec_ref(x_39);
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_2);
return x_43;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_33);
x_62 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0;
x_63 = lean_string_append(x_11, x_62);
lean_inc(x_8);
x_64 = l_Nat_reprFast(x_8);
x_65 = lean_string_append(x_63, x_64);
x_66 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__3;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_64);
lean_dec_ref(x_64);
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2;
x_70 = lean_string_append(x_68, x_69);
x_71 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_72 = lean_string_append(x_70, x_71);
x_12 = x_4;
x_13 = x_72;
goto block_17;
}
}
block_84:
{
if (x_75 == 0)
{
x_33 = x_74;
x_34 = x_75;
goto block_73;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_74);
x_76 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0;
x_77 = lean_string_append(x_11, x_76);
lean_inc(x_8);
x_78 = l_Nat_reprFast(x_8);
x_79 = lean_string_append(x_77, x_78);
lean_dec_ref(x_78);
x_80 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__4;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_83 = lean_string_append(x_81, x_82);
x_12 = x_4;
x_13 = x_83;
goto block_17;
}
}
block_87:
{
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_array_fget_borrowed(x_1, x_8);
switch (lean_obj_tag(x_86)) {
case 6:
{
x_74 = x_86;
x_75 = x_5;
goto block_84;
}
case 13:
{
x_74 = x_86;
x_75 = x_5;
goto block_84;
}
default: 
{
lean_inc(x_86);
x_33 = x_86;
x_34 = x_85;
goto block_73;
}
}
}
else
{
x_12 = x_4;
x_13 = x_11;
goto block_17;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_7);
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_13, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("return y;", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" y;", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y.tag = 1;", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("== 0) {", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y.tag = 0;", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (x.tag == 0) {", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y.tag = x.tag;", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("memcpy(y.u, x.u, sizeof(size_t)*", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructReshapeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_3, x_4);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_IR_EmitC_compatibleReshape(x_1, x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_22 = lean_box(0);
x_23 = l_Lean_IR_EmitC_emitFnDeclAux___closed__4;
x_24 = lean_string_append(x_6, x_23);
lean_inc(x_4);
x_25 = l_Lean_IR_EmitC_structType(x_4);
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0;
x_30 = lean_string_append(x_28, x_29);
lean_inc(x_3);
x_31 = l_Nat_reprFast(x_3);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Nat_reprFast(x_4);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Lean_IR_EmitC_structType(x_3);
x_40 = lean_string_append(x_38, x_39);
lean_dec_ref(x_39);
x_41 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__5;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_25);
lean_dec_ref(x_25);
x_46 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_string_append(x_47, x_43);
switch (lean_obj_tag(x_1)) {
case 11:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_2, 1);
x_51 = lean_box(x_18);
lean_inc_ref(x_50);
lean_inc_ref(x_49);
x_52 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___boxed), 8, 5);
lean_closure_set(x_52, 0, x_22);
lean_closure_set(x_52, 1, x_49);
lean_closure_set(x_52, 2, x_50);
lean_closure_set(x_52, 3, x_51);
lean_closure_set(x_52, 4, x_43);
x_53 = l_Lean_IR_EmitC_optionLike_x3f(x_1);
lean_dec_ref(x_1);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_64; lean_object* x_65; uint8_t x_74; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_107 = lean_array_get_borrowed(x_22, x_49, x_55);
x_108 = lean_array_get_borrowed(x_22, x_50, x_55);
x_109 = l_Lean_IR_EmitC_compatibleReshape(x_107, x_108);
if (x_109 == 0)
{
x_74 = x_19;
goto block_106;
}
else
{
x_74 = x_18;
goto block_106;
}
block_63:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = l_Lean_IR_EmitC_emitStructReshapeFn___lam__0(x_22, x_49, x_50, x_18, x_43, x_55, x_56, x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_43);
x_7 = x_62;
goto block_17;
}
block_73:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_43);
x_69 = l_Lean_IR_EmitC_optionLike_x3f(x_2);
lean_dec_ref(x_2);
if (lean_obj_tag(x_69) == 0)
{
if (x_19 == 0)
{
x_56 = x_64;
x_57 = x_68;
goto block_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__2;
x_71 = lean_string_append(x_68, x_70);
x_72 = lean_string_append(x_71, x_43);
x_56 = x_64;
x_57 = x_72;
goto block_63;
}
}
else
{
lean_dec_ref(x_69);
x_56 = x_64;
x_57 = x_68;
goto block_63;
}
}
block_106:
{
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc_ref(x_50);
x_75 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__0;
x_76 = lean_string_append(x_48, x_75);
x_77 = l_Lean_IR_EmitC_emitPath(x_54, x_5, x_76);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__3;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_string_append(x_80, x_43);
x_82 = l_Lean_IR_EmitC_optionLike_x3f(x_2);
if (lean_obj_tag(x_82) == 1)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__4;
x_85 = lean_string_append(x_81, x_84);
x_86 = l_Lean_IR_EmitC_emitPath(x_83, x_5, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_IR_EmitC_emitCtor___closed__3;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_43);
x_64 = x_5;
x_65 = x_90;
goto block_73;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
x_91 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__5;
x_92 = lean_string_append(x_81, x_91);
x_93 = lean_string_append(x_92, x_43);
x_64 = x_5;
x_65 = x_93;
goto block_73;
}
}
else
{
lean_object* x_94; 
lean_dec(x_54);
lean_dec_ref(x_49);
x_94 = l_Lean_IR_EmitC_optionLike_x3f(x_2);
lean_dec_ref(x_2);
if (lean_obj_tag(x_94) == 1)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__4;
x_97 = lean_string_append(x_48, x_96);
x_98 = l_Lean_IR_EmitC_emitPath(x_95, x_5, x_97);
lean_dec_ref(x_5);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = l_Lean_IR_EmitC_emitCtor___closed__3;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_string_append(x_101, x_43);
x_7 = x_102;
goto block_17;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_94);
lean_dec_ref(x_5);
x_103 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__5;
x_104 = lean_string_append(x_48, x_103);
x_105 = lean_string_append(x_104, x_43);
x_7 = x_105;
goto block_17;
}
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_53);
lean_inc_ref(x_50);
x_110 = l_Lean_IR_EmitC_optionLike_x3f(x_2);
lean_dec_ref(x_2);
if (lean_obj_tag(x_110) == 1)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec_ref(x_52);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_unsigned_to_nat(1u);
x_140 = lean_array_get_borrowed(x_22, x_49, x_112);
x_141 = lean_array_get_borrowed(x_22, x_50, x_112);
x_142 = l_Lean_IR_EmitC_compatibleReshape(x_140, x_141);
if (x_142 == 0)
{
x_113 = x_19;
goto block_139;
}
else
{
x_113 = x_18;
goto block_139;
}
block_139:
{
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_114 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__6;
x_115 = lean_string_append(x_48, x_114);
x_116 = lean_string_append(x_115, x_43);
x_117 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__4;
x_118 = lean_string_append(x_116, x_117);
x_119 = l_Lean_IR_EmitC_emitPath(x_111, x_5, x_118);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = l_Lean_IR_EmitC_emitCtor___closed__3;
x_122 = lean_string_append(x_120, x_121);
x_123 = lean_string_append(x_122, x_43);
x_124 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_string_append(x_125, x_43);
x_127 = l_Lean_IR_EmitC_emitStructReshapeFn___lam__0(x_22, x_49, x_50, x_18, x_43, x_112, x_5, x_126);
lean_dec_ref(x_5);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_string_append(x_130, x_43);
x_7 = x_131;
goto block_17;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_132 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__4;
x_133 = lean_string_append(x_48, x_132);
x_134 = l_Lean_IR_EmitC_emitPath(x_111, x_5, x_133);
lean_dec_ref(x_5);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Lean_IR_EmitC_emitCtor___closed__3;
x_137 = lean_string_append(x_135, x_136);
x_138 = lean_string_append(x_137, x_43);
x_7 = x_138;
goto block_17;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_110);
x_143 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitStructReshapeFn___lam__1), 5, 1);
lean_closure_set(x_143, 0, x_52);
lean_inc_ref(x_49);
x_144 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitStructReshapeFn___lam__2___boxed), 4, 3);
lean_closure_set(x_144, 0, x_22);
lean_closure_set(x_144, 1, x_49);
lean_closure_set(x_144, 2, x_50);
x_145 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__7;
x_146 = lean_string_append(x_48, x_145);
x_147 = lean_string_append(x_146, x_43);
x_148 = lean_array_get_size(x_49);
lean_dec_ref(x_49);
x_149 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__3;
x_150 = l_Lean_IR_EmitC_emitUnionSwitchWithImpossible(x_148, x_149, x_144, x_143, x_5, x_147);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec_ref(x_150);
x_7 = x_151;
goto block_17;
}
else
{
return x_150;
}
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = x_48;
goto block_17;
}
}
case 10:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_176; uint8_t x_177; uint8_t x_180; 
x_152 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_1, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_1, 3);
lean_inc(x_154);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_155);
lean_dec_ref(x_2);
x_176 = lean_unsigned_to_nat(0u);
x_180 = lean_nat_dec_eq(x_153, x_176);
if (x_180 == 0)
{
x_177 = x_19;
goto block_179;
}
else
{
x_177 = x_18;
goto block_179;
}
block_163:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_array_get_size(x_152);
x_159 = lean_unsigned_to_nat(0u);
x_160 = lean_box(0);
x_161 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg(x_152, x_22, x_155, x_160, x_19, x_158, x_18, x_159, x_160, x_156, x_157);
lean_dec_ref(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_152);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec_ref(x_161);
x_7 = x_162;
goto block_17;
}
else
{
return x_161;
}
}
block_175:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_164 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__8;
x_165 = lean_string_append(x_48, x_164);
x_166 = l_Nat_reprFast(x_153);
x_167 = lean_string_append(x_165, x_166);
lean_dec_ref(x_166);
x_168 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__9;
x_169 = lean_string_append(x_167, x_168);
x_170 = l_Nat_reprFast(x_154);
x_171 = lean_string_append(x_169, x_170);
lean_dec_ref(x_170);
x_172 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_string_append(x_173, x_43);
x_156 = x_5;
x_157 = x_174;
goto block_163;
}
block_179:
{
if (x_177 == 0)
{
uint8_t x_178; 
x_178 = lean_nat_dec_eq(x_154, x_176);
if (x_178 == 0)
{
if (x_19 == 0)
{
lean_dec(x_154);
lean_dec(x_153);
x_156 = x_5;
x_157 = x_48;
goto block_163;
}
else
{
goto block_175;
}
}
else
{
lean_dec(x_154);
lean_dec(x_153);
x_156 = x_5;
x_157 = x_48;
goto block_163;
}
}
else
{
goto block_175;
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = x_48;
goto block_17;
}
}
default: 
{
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_48;
goto block_17;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_6);
return x_182;
}
block_17:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_string_append(x_13, x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_5);
x_16 = lean_unbox(x_7);
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0(x_1, x_2, x_3, x_4, x_15, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_ctor_set(y, ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_box(0));", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_7, x_1);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_37; 
x_19 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__0;
x_20 = lean_string_append(x_10, x_19);
lean_inc(x_7);
x_21 = l_Nat_reprFast(x_7);
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_2);
x_37 = lean_array_fget_borrowed(x_6, x_7);
switch (lean_obj_tag(x_37)) {
case 6:
{
lean_dec_ref(x_21);
goto block_36;
}
case 13:
{
lean_dec_ref(x_21);
goto block_36;
}
default: 
{
switch (lean_obj_tag(x_37)) {
case 7:
{
goto block_31;
}
case 8:
{
goto block_31;
}
case 12:
{
goto block_31;
}
default: 
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(8);
lean_inc(x_37);
x_39 = l_Lean_IR_EmitC_emitBoxFn(x_37, x_38, x_9, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_string_append(x_42, x_3);
x_44 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_21);
lean_dec_ref(x_21);
x_47 = l_Lean_IR_EmitC_emitSProj___closed__0;
x_48 = lean_string_append(x_46, x_47);
x_49 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_50 = lean_string_append(x_48, x_49);
x_11 = x_5;
x_12 = x_50;
goto block_16;
}
else
{
lean_dec_ref(x_21);
lean_dec(x_7);
return x_39;
}
}
}
}
}
block_31:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_string_append(x_23, x_3);
x_25 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_21);
lean_dec_ref(x_21);
x_28 = lean_string_append(x_27, x_4);
x_29 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_30 = lean_string_append(x_28, x_29);
x_11 = x_5;
x_12 = x_30;
goto block_16;
}
block_36:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__1;
x_33 = lean_string_append(x_23, x_32);
x_34 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_35 = lean_string_append(x_33, x_34);
x_11 = x_5;
x_12 = x_35;
goto block_16;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_7, x_13);
lean_dec(x_7);
x_7 = x_14;
x_8 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBox___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("memcpy(lean_ctor_scalar_cptr(y), ", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBox___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".u, sizeof(size_t)*", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBox___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y = lean_alloc_ctor(", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBox___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", sizeof(size_t)*", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBox___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y = lean_box(", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBox___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.EmitC.emitStructBox", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBox___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitUSet___closed__5;
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(1065u);
x_4 = l_Lean_IR_EmitC_emitStructBox___closed__5;
x_5 = l_Lean_IR_EmitC_emitUSet___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_66; uint8_t x_80; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec_ref(x_1);
x_80 = l_Array_isEmpty___redArg(x_6);
if (x_80 == 0)
{
x_66 = x_80;
goto block_79;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_nat_dec_eq(x_7, x_81);
x_66 = x_82;
goto block_79;
}
block_21:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(0);
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg(x_11, x_9, x_3, x_10, x_15, x_6, x_14, x_15, x_12, x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_6);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
return x_16;
}
}
block_40:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = l_Lean_IR_EmitC_emitStructBox___closed__0;
x_31 = lean_string_append(x_27, x_30);
x_32 = lean_string_append(x_31, x_3);
x_33 = l_Lean_IR_EmitC_emitStructBox___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_29);
lean_dec_ref(x_29);
x_36 = lean_string_append(x_35, x_23);
lean_dec_ref(x_23);
x_37 = lean_string_append(x_36, x_28);
lean_dec_ref(x_28);
x_38 = lean_string_append(x_37, x_26);
x_39 = lean_string_append(x_38, x_22);
lean_dec_ref(x_22);
x_9 = x_24;
x_10 = x_26;
x_11 = x_25;
x_12 = x_4;
x_13 = x_39;
goto block_21;
}
block_65:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_41 = l_Lean_IR_EmitC_emitStructBox___closed__2;
x_42 = lean_string_append(x_5, x_41);
x_43 = l_Nat_reprFast(x_2);
x_44 = lean_string_append(x_42, x_43);
lean_dec_ref(x_43);
x_45 = l_Lean_IR_EmitC_emitSpreadArg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_array_get_size(x_6);
x_48 = l_Nat_reprFast(x_47);
x_49 = lean_string_append(x_46, x_48);
lean_dec_ref(x_48);
x_50 = l_Lean_IR_EmitC_emitStructBox___closed__3;
x_51 = lean_string_append(x_49, x_50);
lean_inc(x_7);
x_52 = l_Nat_reprFast(x_7);
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__9;
x_55 = lean_string_append(x_53, x_54);
lean_inc(x_8);
x_56 = l_Nat_reprFast(x_8);
x_57 = lean_string_append(x_55, x_56);
x_58 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_7, x_62);
lean_dec(x_7);
if (x_63 == 0)
{
lean_dec(x_8);
x_22 = x_60;
x_23 = x_54;
x_24 = x_45;
x_25 = x_47;
x_26 = x_58;
x_27 = x_61;
x_28 = x_56;
x_29 = x_52;
goto block_40;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_eq(x_8, x_62);
lean_dec(x_8);
if (x_64 == 0)
{
x_22 = x_60;
x_23 = x_54;
x_24 = x_45;
x_25 = x_47;
x_26 = x_58;
x_27 = x_61;
x_28 = x_56;
x_29 = x_52;
goto block_40;
}
else
{
lean_dec_ref(x_56);
lean_dec_ref(x_52);
x_9 = x_45;
x_10 = x_58;
x_11 = x_47;
x_12 = x_4;
x_13 = x_61;
goto block_21;
}
}
}
block_79:
{
if (x_66 == 0)
{
goto block_65;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_eq(x_8, x_67);
if (x_68 == 0)
{
goto block_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_69 = l_Lean_IR_EmitC_emitStructBox___closed__4;
x_70 = lean_string_append(x_5, x_69);
x_71 = l_Nat_reprFast(x_2);
x_72 = lean_string_append(x_70, x_71);
lean_dec_ref(x_71);
x_73 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_74 = lean_string_append(x_72, x_73);
x_75 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_76 = lean_string_append(x_74, x_75);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_2);
lean_dec(x_1);
x_83 = l_Lean_IR_EmitC_emitStructBox___closed__6;
x_84 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_83, x_4, x_5);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitStructBox(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBoxFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___closed__0;
lean_inc(x_2);
x_8 = l_Nat_reprFast(x_2);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
lean_inc(x_6);
x_10 = l_Lean_IR_EmitC_emitStructBox(x_6, x_2, x_9, x_4, x_5);
lean_dec_ref(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBoxFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitStructBoxFn___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBoxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static lean_object* ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBoxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_object* y;", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBoxFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y = lean_box(0);", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructBoxFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructBoxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_16 = l_Lean_IR_EmitC_emitStructBoxFn___closed__0;
x_17 = lean_string_append(x_4, x_16);
x_18 = l_Lean_IR_EmitC_structBoxFnPrefix___closed__0;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_2);
x_20 = l_Nat_reprFast(x_2);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_structType(x_2);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__5;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitStructBoxFn___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_28);
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_IR_EmitC_optionLike_x3f(x_1);
lean_dec_ref(x_1);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__0;
x_37 = lean_string_append(x_32, x_36);
x_38 = lean_string_append(x_37, x_28);
x_39 = l_Lean_IR_EmitC_emitPath(x_35, x_3, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_box(0);
x_42 = l_Lean_IR_EmitC_emitUnionSwitch___closed__0;
x_43 = lean_string_append(x_40, x_42);
x_44 = l_Lean_IR_EmitC_emitStructBoxFn___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_28);
x_47 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_28);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_array_get(x_41, x_33, x_50);
lean_dec_ref(x_33);
x_52 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__2;
x_53 = l_Lean_IR_EmitC_emitStructBox(x_51, x_50, x_52, x_3, x_49);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_string_append(x_56, x_28);
x_5 = x_57;
goto block_15;
}
else
{
return x_53;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_34);
lean_inc_ref(x_33);
x_58 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitStructBoxFn___lam__0___boxed), 5, 1);
lean_closure_set(x_58, 0, x_33);
x_59 = lean_array_get_size(x_33);
lean_dec_ref(x_33);
x_60 = l_Lean_IR_EmitC_emitStructIncDecFn___closed__3;
x_61 = l_Lean_IR_EmitC_emitUnionSwitch(x_59, x_60, x_58, x_3, x_32);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_5 = x_62;
goto block_15;
}
else
{
return x_61;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_IR_EmitC_emitStructBoxFn___closed__3;
x_65 = l_Lean_IR_EmitC_emitStructBox(x_1, x_63, x_64, x_3, x_32);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_5 = x_66;
goto block_15;
}
else
{
return x_65;
}
}
block_15:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__0;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_string_append(x_11, x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(x);", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__0;
x_8 = lean_string_append(x_6, x_7);
lean_inc(x_3);
x_9 = l_Nat_reprFast(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_array_fget_borrowed(x_1, x_3);
lean_dec(x_3);
x_14 = l_Lean_IR_EmitC_emitUnboxFn(x_13, x_5, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___closed__0;
x_19 = lean_string_append(x_16, x_18);
x_20 = lean_box(0);
x_21 = lean_string_append(x_19, x_2);
lean_ctor_set(x_14, 1, x_21);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___closed__0;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
x_26 = lean_string_append(x_24, x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitStructUnboxFn___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = lean_ctor_get(x, ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(lean_ctor_get(x, ", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_26; 
x_26 = lean_nat_dec_lt(x_4, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_array_fget_borrowed(x_3, x_4);
switch (lean_obj_tag(x_28)) {
case 6:
{
x_8 = x_1;
x_9 = x_7;
goto block_13;
}
case 13:
{
x_8 = x_1;
x_9 = x_7;
goto block_13;
}
default: 
{
switch (lean_obj_tag(x_28)) {
case 7:
{
goto block_25;
}
case 8:
{
goto block_25;
}
case 12:
{
goto block_25;
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0;
x_30 = lean_string_append(x_7, x_29);
lean_inc(x_4);
x_31 = l_Nat_reprFast(x_4);
x_32 = lean_string_append(x_30, x_31);
x_33 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Lean_IR_EmitC_emitUnboxFn(x_28, x_6, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_31);
lean_dec_ref(x_31);
x_40 = l_Lean_IR_EmitC_emitSProj___closed__0;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_43 = lean_string_append(x_41, x_42);
x_8 = x_1;
x_9 = x_43;
goto block_13;
}
else
{
lean_dec_ref(x_31);
lean_dec(x_4);
return x_35;
}
}
}
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
block_25:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0;
x_15 = lean_string_append(x_7, x_14);
lean_inc(x_4);
x_16 = l_Nat_reprFast(x_4);
x_17 = lean_string_append(x_15, x_16);
x_18 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_16);
lean_dec_ref(x_16);
x_21 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_24 = lean_string_append(x_22, x_23);
x_8 = x_1;
x_9 = x_24;
goto block_13;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(lean_object* x) {", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (lean_is_scalar(x)) {", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y.cs.c1 = ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y.tag = lean_obj_tag(x);", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y.tag", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("memcpy(y.u, lean_ctor_scalar_cptr(x), sizeof(size_t)*", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.EmitC.emitStructUnboxFn", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitUSet___closed__5;
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_unsigned_to_nat(1128u);
x_4 = l_Lean_IR_EmitC_emitStructUnboxFn___closed__6;
x_5 = l_Lean_IR_EmitC_emitUSet___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructUnboxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_16 = l_Lean_IR_EmitC_emitFnDeclAux___closed__4;
x_17 = lean_string_append(x_4, x_16);
lean_inc(x_2);
x_18 = l_Lean_IR_EmitC_structType(x_2);
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_IR_EmitC_structUnboxFnPrefix___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_2);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_EmitC_emitStructUnboxFn___closed__0;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_18);
lean_dec_ref(x_18);
x_31 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_28);
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_34);
x_35 = l_Lean_IR_EmitC_optionLike_x3f(x_1);
lean_dec_ref(x_1);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_IR_EmitC_emitStructUnboxFn___closed__1;
x_38 = lean_string_append(x_33, x_37);
x_39 = lean_string_append(x_38, x_28);
x_40 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__4;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lean_IR_EmitC_emitPath(x_36, x_3, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_box(0);
x_45 = l_Lean_IR_EmitC_emitCtor___closed__3;
x_46 = lean_string_append(x_43, x_45);
x_47 = lean_string_append(x_46, x_28);
x_48 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_28);
x_51 = l_Lean_IR_EmitC_emitStructUnboxFn___closed__2;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_array_get(x_44, x_34, x_53);
lean_dec_ref(x_34);
x_55 = l_Lean_IR_EmitC_emitUnboxFn(x_54, x_3, x_52);
lean_dec_ref(x_3);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___closed__0;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_28);
x_60 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_28);
x_5 = x_62;
goto block_15;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_35);
lean_inc_ref(x_34);
x_63 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___boxed), 6, 2);
lean_closure_set(x_63, 0, x_34);
lean_closure_set(x_63, 1, x_28);
x_64 = l_Lean_IR_EmitC_emitStructUnboxFn___closed__3;
x_65 = lean_string_append(x_33, x_64);
x_66 = lean_string_append(x_65, x_28);
x_67 = lean_array_get_size(x_34);
lean_dec_ref(x_34);
x_68 = l_Lean_IR_EmitC_emitStructUnboxFn___closed__4;
x_69 = l_Lean_IR_EmitC_emitUnionSwitch(x_67, x_68, x_63, x_3, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_5 = x_70;
goto block_15;
}
else
{
return x_69;
}
}
}
else
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_94; uint8_t x_95; 
x_71 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 3);
lean_inc(x_73);
lean_dec_ref(x_1);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_eq(x_72, x_94);
if (x_95 == 0)
{
goto block_93;
}
else
{
uint8_t x_96; 
x_96 = lean_nat_dec_eq(x_73, x_94);
if (x_96 == 0)
{
goto block_93;
}
else
{
lean_dec(x_73);
lean_dec(x_72);
x_74 = x_3;
x_75 = x_33;
goto block_81;
}
}
block_81:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_array_get_size(x_71);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_box(0);
x_79 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg(x_78, x_76, x_71, x_77, x_78, x_74, x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_71);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_5 = x_80;
goto block_15;
}
else
{
return x_79;
}
}
block_93:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_82 = l_Lean_IR_EmitC_emitStructUnboxFn___closed__5;
x_83 = lean_string_append(x_33, x_82);
x_84 = l_Nat_reprFast(x_72);
x_85 = lean_string_append(x_83, x_84);
lean_dec_ref(x_84);
x_86 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__9;
x_87 = lean_string_append(x_85, x_86);
x_88 = l_Nat_reprFast(x_73);
x_89 = lean_string_append(x_87, x_88);
lean_dec_ref(x_88);
x_90 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_string_append(x_91, x_28);
x_74 = x_3;
x_75 = x_92;
goto block_81;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_1);
x_97 = l_Lean_IR_EmitC_emitStructUnboxFn___closed__7;
x_98 = l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0(x_97, x_3, x_33);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_5 = x_99;
goto block_15;
}
else
{
return x_98;
}
}
}
block_15:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_IR_EmitC_emitStructReshapeFn___closed__0;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_string_append(x_11, x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructDeclsFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_inc(x_1);
x_12 = l_Lean_IR_EmitC_structType(x_1);
lean_inc_ref(x_3);
lean_inc(x_5);
x_13 = l_Lean_IR_EmitC_emitStructDefn(x_5, x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_EmitC_needsRC(x_5);
if (x_15 == 0)
{
x_6 = x_3;
x_7 = x_14;
goto block_11;
}
else
{
lean_object* x_16; 
lean_inc_ref(x_3);
lean_inc(x_1);
lean_inc(x_5);
x_16 = l_Lean_IR_EmitC_emitStructIncDecFn(x_5, x_1, x_15, x_3, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = 0;
lean_inc_ref(x_3);
lean_inc(x_1);
lean_inc(x_5);
x_19 = l_Lean_IR_EmitC_emitStructIncDecFn(x_5, x_1, x_18, x_3, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_6 = x_3;
x_7 = x_20;
goto block_11;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_16;
}
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_13;
}
block_11:
{
lean_object* x_8; 
lean_inc_ref(x_6);
lean_inc(x_1);
lean_inc(x_5);
x_8 = l_Lean_IR_EmitC_emitStructBoxFn(x_5, x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_IR_EmitC_emitStructUnboxFn(x_5, x_1, x_6, x_9);
return x_10;
}
else
{
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget_borrowed(x_2, x_4);
lean_inc_ref(x_6);
lean_inc(x_10);
lean_inc(x_4);
x_11 = l_Lean_IR_EmitC_emitStructDeclsFor(x_4, x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
{
lean_object* _tmp_3 = x_14;
lean_object* _tmp_4 = x_3;
lean_object* _tmp_6 = x_12;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_dec_ref(x_6);
lean_dec(x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitStructDecls_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_8, x_7);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_10);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_array_uget(x_6, x_8);
lean_inc_ref(x_2);
x_16 = lean_array_get_borrowed(x_2, x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_10);
lean_inc(x_4);
lean_inc(x_17);
lean_inc(x_14);
x_18 = l_Lean_IR_EmitC_emitStructReshapeFn(x_14, x_17, x_4, x_15, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_8, x_20);
{
size_t _tmp_7 = x_21;
lean_object* _tmp_8 = x_5;
lean_object* _tmp_10 = x_19;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec_ref(x_10);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitStructDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitStructDecls_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_13, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_array_fget_borrowed(x_2, x_5);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_array_size(x_12);
x_14 = 0;
lean_inc_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc(x_11);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitStructDecls_spec__0(x_11, x_3, x_2, x_5, x_4, x_12, x_13, x_14, x_4, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
{
lean_object* _tmp_4 = x_18;
lean_object* _tmp_5 = x_4;
lean_object* _tmp_7 = x_16;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructDecls___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 6);
lean_dec(x_6);
lean_inc_ref(x_5);
x_7 = l_Lean_IR_getDecls(x_5);
x_8 = l_Lean_IR_collectStructTypes(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_box(0);
lean_ctor_set(x_2, 6, x_10);
lean_inc_ref(x_2);
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___redArg(x_11, x_9, x_13, x_12, x_13, x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_IR_instInhabitedStructTypeInfo_default;
lean_inc_ref(x_2);
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___redArg(x_11, x_9, x_16, x_13, x_12, x_13, x_2, x_15);
lean_dec(x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_apply_2(x_1, x_2, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_2);
lean_dec(x_9);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_ctor_get(x_2, 3);
x_32 = lean_ctor_get(x_2, 4);
x_33 = lean_ctor_get(x_2, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
lean_inc_ref(x_28);
x_34 = l_Lean_IR_getDecls(x_28);
x_35 = l_Lean_IR_collectStructTypes(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_array_get_size(x_36);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_37);
lean_inc_ref(x_41);
x_42 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___redArg(x_38, x_36, x_40, x_39, x_40, x_41, x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_IR_instInhabitedStructTypeInfo_default;
lean_inc_ref(x_41);
x_45 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___redArg(x_38, x_36, x_44, x_40, x_39, x_40, x_41, x_43);
lean_dec(x_36);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_apply_2(x_1, x_41, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_41);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_41);
lean_dec(x_36);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitStructDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitStructDecls___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDecls_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_object* ", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = _args[", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_instInhabitedParam_default;
x_14 = lean_array_get_borrowed(x_13, x_1, x_12);
x_15 = lean_ctor_get(x_14, 0);
x_16 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0;
x_17 = lean_string_append(x_4, x_16);
x_18 = l_Lean_IR_EmitC_argToCString___closed__0;
lean_inc(x_15);
x_19 = l_Nat_reprFast(x_15);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = lean_string_append(x_17, x_20);
lean_dec_ref(x_20);
x_22 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_EmitC_emitUProj___closed__0;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_29 = lean_string_append(x_27, x_28);
x_3 = x_10;
x_4 = x_29;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_start:", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_object** _args", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("()", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc_ref(x_1);
x_4 = l_Lean_IR_mkVarJPMaps(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 5);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_dec(x_15);
x_16 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_16);
lean_inc_ref(x_9);
x_17 = l_Lean_hasInitAttr(x_9, x_16);
if (x_17 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_73; lean_object* x_74; lean_object* x_84; lean_object* x_85; lean_object* x_89; 
lean_free_object(x_4);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec_ref(x_1);
lean_ctor_set(x_2, 5, x_7);
lean_ctor_set(x_2, 2, x_8);
lean_inc_ref(x_2);
lean_inc(x_18);
x_89 = l_Lean_IR_EmitC_toCName(x_18, x_2, x_3);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_113; lean_object* x_114; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = 1;
x_138 = lean_array_get_size(x_19);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
x_142 = lean_string_append(x_91, x_141);
x_113 = x_2;
x_114 = x_142;
goto block_137;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Lean_IR_EmitC_emitFnDeclAux___closed__4;
x_144 = lean_string_append(x_91, x_143);
x_113 = x_2;
x_114 = x_144;
goto block_137;
}
block_101:
{
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = l_Lean_IR_EmitC_emitSpreadArgs(x_94, x_92, x_93, x_95);
lean_dec_ref(x_94);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_84 = x_93;
x_85 = x_98;
goto block_88;
}
else
{
lean_dec_ref(x_93);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_16);
return x_97;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_94);
x_99 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_100 = lean_string_append(x_95, x_99);
x_84 = x_93;
x_85 = x_100;
goto block_88;
}
}
block_112:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = lean_string_append(x_103, x_90);
lean_dec(x_90);
x_106 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_107 = lean_string_append(x_105, x_106);
x_108 = l_Lean_closureMaxArgs;
x_109 = lean_array_get_size(x_104);
x_110 = lean_nat_dec_lt(x_108, x_109);
if (x_110 == 0)
{
x_93 = x_102;
x_94 = x_104;
x_95 = x_107;
x_96 = x_110;
goto block_101;
}
else
{
uint8_t x_111; 
x_111 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_16);
x_93 = x_102;
x_94 = x_104;
x_95 = x_107;
x_96 = x_111;
goto block_101;
}
}
block_137:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_115 = l_Lean_IR_EmitC_toCType(x_20, x_113, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec_ref(x_115);
x_118 = lean_string_append(x_117, x_116);
lean_dec(x_116);
x_119 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_array_get_size(x_19);
x_123 = lean_nat_dec_lt(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = l_Lean_IR_EmitC_toCInitName___closed__0;
x_125 = lean_string_append(x_124, x_90);
lean_dec(x_90);
x_126 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_127 = lean_string_append(x_125, x_126);
x_128 = lean_string_append(x_120, x_127);
lean_dec_ref(x_127);
x_73 = x_113;
x_74 = x_128;
goto block_83;
}
else
{
lean_object* x_129; 
x_129 = l_Lean_IR_EmitC_emitFnDeclAux___closed__2;
if (x_123 == 0)
{
x_102 = x_113;
x_103 = x_120;
x_104 = x_129;
goto block_112;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_122, x_122);
if (x_130 == 0)
{
if (x_123 == 0)
{
x_102 = x_113;
x_103 = x_120;
x_104 = x_129;
goto block_112;
}
else
{
size_t x_131; size_t x_132; lean_object* x_133; 
x_131 = 0;
x_132 = lean_usize_of_nat(x_122);
x_133 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_19, x_131, x_132, x_129);
x_102 = x_113;
x_103 = x_120;
x_104 = x_133;
goto block_112;
}
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; 
x_134 = 0;
x_135 = lean_usize_of_nat(x_122);
x_136 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_19, x_134, x_135, x_129);
x_102 = x_113;
x_103 = x_120;
x_104 = x_136;
goto block_112;
}
}
}
}
}
else
{
uint8_t x_145; 
lean_dec_ref(x_2);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_16);
x_145 = !lean_is_exclusive(x_89);
if (x_145 == 0)
{
return x_89;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_89, 0);
x_147 = lean_ctor_get(x_89, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_89);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
block_65:
{
lean_object* x_24; 
x_24 = l_Lean_IR_EmitC_emitSpreads(x_19, x_22, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_22, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 3);
lean_dec(x_28);
x_29 = l_Lean_IR_EmitC_emitDeclAux___closed__0;
x_30 = lean_string_append(x_25, x_29);
x_31 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_32 = lean_string_append(x_30, x_31);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 3, x_18);
x_33 = l_Lean_IR_EmitC_emitFnBody(x_21, x_22, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_38 = lean_string_append(x_35, x_37);
x_39 = lean_box(0);
x_40 = lean_string_append(x_38, x_31);
lean_ctor_set(x_33, 1, x_40);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_box(0);
x_45 = lean_string_append(x_43, x_31);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
return x_33;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
x_49 = lean_ctor_get(x_22, 2);
x_50 = lean_ctor_get(x_22, 5);
x_51 = lean_ctor_get(x_22, 6);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_52 = l_Lean_IR_EmitC_emitDeclAux___closed__0;
x_53 = lean_string_append(x_25, x_52);
x_54 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_18);
lean_ctor_set(x_56, 4, x_19);
lean_ctor_set(x_56, 5, x_50);
lean_ctor_set(x_56, 6, x_51);
x_57 = l_Lean_IR_EmitC_emitFnBody(x_21, x_56, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_61 = lean_string_append(x_58, x_60);
x_62 = lean_box(0);
x_63 = lean_string_append(x_61, x_54);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
return x_57;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_18);
return x_24;
}
}
block_72:
{
if (x_69 == 0)
{
lean_dec(x_68);
x_22 = x_66;
x_23 = x_67;
goto block_65;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_inc(x_68);
x_70 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(x_19, x_68, x_68, x_67);
lean_dec(x_68);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec_ref(x_70);
x_22 = x_66;
x_23 = x_71;
goto block_65;
}
}
block_83:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_75 = l_Lean_IR_EmitC_emitStructDefn___closed__0;
x_76 = lean_string_append(x_74, x_75);
x_77 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_78 = lean_string_append(x_76, x_77);
x_79 = l_Lean_closureMaxArgs;
x_80 = lean_array_get_size(x_19);
x_81 = lean_nat_dec_lt(x_79, x_80);
if (x_81 == 0)
{
lean_dec(x_16);
x_66 = x_73;
x_67 = x_78;
x_68 = x_80;
x_69 = x_81;
goto block_72;
}
else
{
uint8_t x_82; 
x_82 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_16);
lean_dec(x_16);
x_66 = x_73;
x_67 = x_78;
x_68 = x_80;
x_69 = x_82;
goto block_72;
}
}
block_88:
{
lean_object* x_86; lean_object* x_87; 
x_86 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_87 = lean_string_append(x_85, x_86);
x_73 = x_84;
x_74 = x_87;
goto block_83;
}
}
else
{
lean_object* x_149; 
lean_dec(x_16);
lean_free_object(x_2);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_149 = lean_box(0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_149);
return x_4;
}
}
else
{
lean_object* x_150; 
lean_dec(x_16);
lean_free_object(x_2);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_150 = lean_box(0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_150);
return x_4;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = lean_ctor_get(x_4, 0);
x_152 = lean_ctor_get(x_4, 1);
x_153 = lean_ctor_get(x_2, 0);
x_154 = lean_ctor_get(x_2, 1);
x_155 = lean_ctor_get(x_2, 3);
x_156 = lean_ctor_get(x_2, 4);
x_157 = lean_ctor_get(x_2, 6);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_2);
x_158 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_158);
lean_inc_ref(x_153);
x_159 = l_Lean_hasInitAttr(x_153, x_158);
if (x_159 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_195; lean_object* x_196; lean_object* x_206; lean_object* x_207; lean_object* x_211; lean_object* x_212; 
lean_free_object(x_4);
x_160 = lean_ctor_get(x_1, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_1, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_1, 3);
lean_inc(x_163);
lean_dec_ref(x_1);
x_211 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_211, 0, x_153);
lean_ctor_set(x_211, 1, x_154);
lean_ctor_set(x_211, 2, x_152);
lean_ctor_set(x_211, 3, x_155);
lean_ctor_set(x_211, 4, x_156);
lean_ctor_set(x_211, 5, x_151);
lean_ctor_set(x_211, 6, x_157);
lean_inc_ref(x_211);
lean_inc(x_160);
x_212 = l_Lean_IR_EmitC_toCName(x_160, x_211, x_3);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_236; lean_object* x_237; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
x_215 = 1;
x_261 = lean_array_get_size(x_161);
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_nat_dec_eq(x_261, x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
x_265 = lean_string_append(x_214, x_264);
x_236 = x_211;
x_237 = x_265;
goto block_260;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = l_Lean_IR_EmitC_emitFnDeclAux___closed__4;
x_267 = lean_string_append(x_214, x_266);
x_236 = x_211;
x_237 = x_267;
goto block_260;
}
block_224:
{
if (x_219 == 0)
{
lean_object* x_220; 
x_220 = l_Lean_IR_EmitC_emitSpreadArgs(x_217, x_215, x_216, x_218);
lean_dec_ref(x_217);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec_ref(x_220);
x_206 = x_216;
x_207 = x_221;
goto block_210;
}
else
{
lean_dec_ref(x_216);
lean_dec(x_163);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec(x_158);
return x_220;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec_ref(x_217);
x_222 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_223 = lean_string_append(x_218, x_222);
x_206 = x_216;
x_207 = x_223;
goto block_210;
}
}
block_235:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_228 = lean_string_append(x_226, x_213);
lean_dec(x_213);
x_229 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_230 = lean_string_append(x_228, x_229);
x_231 = l_Lean_closureMaxArgs;
x_232 = lean_array_get_size(x_227);
x_233 = lean_nat_dec_lt(x_231, x_232);
if (x_233 == 0)
{
x_216 = x_225;
x_217 = x_227;
x_218 = x_230;
x_219 = x_233;
goto block_224;
}
else
{
uint8_t x_234; 
x_234 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_158);
x_216 = x_225;
x_217 = x_227;
x_218 = x_230;
x_219 = x_234;
goto block_224;
}
}
block_260:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_238 = l_Lean_IR_EmitC_toCType(x_162, x_236, x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
x_241 = lean_string_append(x_240, x_239);
lean_dec(x_239);
x_242 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_243 = lean_string_append(x_241, x_242);
x_244 = lean_unsigned_to_nat(0u);
x_245 = lean_array_get_size(x_161);
x_246 = lean_nat_dec_lt(x_244, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = l_Lean_IR_EmitC_toCInitName___closed__0;
x_248 = lean_string_append(x_247, x_213);
lean_dec(x_213);
x_249 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_250 = lean_string_append(x_248, x_249);
x_251 = lean_string_append(x_243, x_250);
lean_dec_ref(x_250);
x_195 = x_236;
x_196 = x_251;
goto block_205;
}
else
{
lean_object* x_252; 
x_252 = l_Lean_IR_EmitC_emitFnDeclAux___closed__2;
if (x_246 == 0)
{
x_225 = x_236;
x_226 = x_243;
x_227 = x_252;
goto block_235;
}
else
{
uint8_t x_253; 
x_253 = lean_nat_dec_le(x_245, x_245);
if (x_253 == 0)
{
if (x_246 == 0)
{
x_225 = x_236;
x_226 = x_243;
x_227 = x_252;
goto block_235;
}
else
{
size_t x_254; size_t x_255; lean_object* x_256; 
x_254 = 0;
x_255 = lean_usize_of_nat(x_245);
x_256 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_161, x_254, x_255, x_252);
x_225 = x_236;
x_226 = x_243;
x_227 = x_256;
goto block_235;
}
}
else
{
size_t x_257; size_t x_258; lean_object* x_259; 
x_257 = 0;
x_258 = lean_usize_of_nat(x_245);
x_259 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_161, x_257, x_258, x_252);
x_225 = x_236;
x_226 = x_243;
x_227 = x_259;
goto block_235;
}
}
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec_ref(x_211);
lean_dec(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec(x_158);
x_268 = lean_ctor_get(x_212, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_212, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_270 = x_212;
} else {
 lean_dec_ref(x_212);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
block_187:
{
lean_object* x_166; 
x_166 = l_Lean_IR_EmitC_emitSpreads(x_161, x_164, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_164, 2);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_164, 5);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_164, 6);
lean_inc_ref(x_172);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 lean_ctor_release(x_164, 4);
 lean_ctor_release(x_164, 5);
 lean_ctor_release(x_164, 6);
 x_173 = x_164;
} else {
 lean_dec_ref(x_164);
 x_173 = lean_box(0);
}
x_174 = l_Lean_IR_EmitC_emitDeclAux___closed__0;
x_175 = lean_string_append(x_167, x_174);
x_176 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_177 = lean_string_append(x_175, x_176);
if (lean_is_scalar(x_173)) {
 x_178 = lean_alloc_ctor(0, 7, 0);
} else {
 x_178 = x_173;
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_178, 2, x_170);
lean_ctor_set(x_178, 3, x_160);
lean_ctor_set(x_178, 4, x_161);
lean_ctor_set(x_178, 5, x_171);
lean_ctor_set(x_178, 6, x_172);
x_179 = l_Lean_IR_EmitC_emitFnBody(x_163, x_178, x_177);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_183 = lean_string_append(x_180, x_182);
x_184 = lean_box(0);
x_185 = lean_string_append(x_183, x_176);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
return x_179;
}
}
else
{
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_161);
lean_dec(x_160);
return x_166;
}
}
block_194:
{
if (x_191 == 0)
{
lean_dec(x_190);
x_164 = x_188;
x_165 = x_189;
goto block_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_inc(x_190);
x_192 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(x_161, x_190, x_190, x_189);
lean_dec(x_190);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec_ref(x_192);
x_164 = x_188;
x_165 = x_193;
goto block_187;
}
}
block_205:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_197 = l_Lean_IR_EmitC_emitStructDefn___closed__0;
x_198 = lean_string_append(x_196, x_197);
x_199 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_200 = lean_string_append(x_198, x_199);
x_201 = l_Lean_closureMaxArgs;
x_202 = lean_array_get_size(x_161);
x_203 = lean_nat_dec_lt(x_201, x_202);
if (x_203 == 0)
{
lean_dec(x_158);
x_188 = x_195;
x_189 = x_200;
x_190 = x_202;
x_191 = x_203;
goto block_194;
}
else
{
uint8_t x_204; 
x_204 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_158);
lean_dec(x_158);
x_188 = x_195;
x_189 = x_200;
x_190 = x_202;
x_191 = x_204;
goto block_194;
}
}
block_210:
{
lean_object* x_208; lean_object* x_209; 
x_208 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_209 = lean_string_append(x_207, x_208);
x_195 = x_206;
x_196 = x_209;
goto block_205;
}
}
else
{
lean_object* x_272; 
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec_ref(x_1);
x_272 = lean_box(0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_272);
return x_4;
}
}
else
{
lean_object* x_273; 
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec_ref(x_1);
x_273 = lean_box(0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_273);
return x_4;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_274 = lean_ctor_get(x_4, 0);
x_275 = lean_ctor_get(x_4, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_4);
x_276 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_2, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_2, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_279);
x_280 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_280);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_281 = x_2;
} else {
 lean_dec_ref(x_2);
 x_281 = lean_box(0);
}
x_282 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_282);
lean_inc_ref(x_276);
x_283 = l_Lean_hasInitAttr(x_276, x_282);
if (x_283 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_319; lean_object* x_320; lean_object* x_330; lean_object* x_331; lean_object* x_335; lean_object* x_336; 
x_284 = lean_ctor_get(x_1, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_285);
x_286 = lean_ctor_get(x_1, 2);
lean_inc(x_286);
x_287 = lean_ctor_get(x_1, 3);
lean_inc(x_287);
lean_dec_ref(x_1);
if (lean_is_scalar(x_281)) {
 x_335 = lean_alloc_ctor(0, 7, 0);
} else {
 x_335 = x_281;
}
lean_ctor_set(x_335, 0, x_276);
lean_ctor_set(x_335, 1, x_277);
lean_ctor_set(x_335, 2, x_275);
lean_ctor_set(x_335, 3, x_278);
lean_ctor_set(x_335, 4, x_279);
lean_ctor_set(x_335, 5, x_274);
lean_ctor_set(x_335, 6, x_280);
lean_inc_ref(x_335);
lean_inc(x_284);
x_336 = l_Lean_IR_EmitC_toCName(x_284, x_335, x_3);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_360; lean_object* x_361; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec_ref(x_336);
x_339 = 1;
x_385 = lean_array_get_size(x_285);
x_386 = lean_unsigned_to_nat(0u);
x_387 = lean_nat_dec_eq(x_385, x_386);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; 
x_388 = l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
x_389 = lean_string_append(x_338, x_388);
x_360 = x_335;
x_361 = x_389;
goto block_384;
}
else
{
lean_object* x_390; lean_object* x_391; 
x_390 = l_Lean_IR_EmitC_emitFnDeclAux___closed__4;
x_391 = lean_string_append(x_338, x_390);
x_360 = x_335;
x_361 = x_391;
goto block_384;
}
block_348:
{
if (x_343 == 0)
{
lean_object* x_344; 
x_344 = l_Lean_IR_EmitC_emitSpreadArgs(x_341, x_339, x_340, x_342);
lean_dec_ref(x_341);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec_ref(x_344);
x_330 = x_340;
x_331 = x_345;
goto block_334;
}
else
{
lean_dec_ref(x_340);
lean_dec(x_287);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec(x_282);
return x_344;
}
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec_ref(x_341);
x_346 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_347 = lean_string_append(x_342, x_346);
x_330 = x_340;
x_331 = x_347;
goto block_334;
}
}
block_359:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_352 = lean_string_append(x_350, x_337);
lean_dec(x_337);
x_353 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_354 = lean_string_append(x_352, x_353);
x_355 = l_Lean_closureMaxArgs;
x_356 = lean_array_get_size(x_351);
x_357 = lean_nat_dec_lt(x_355, x_356);
if (x_357 == 0)
{
x_340 = x_349;
x_341 = x_351;
x_342 = x_354;
x_343 = x_357;
goto block_348;
}
else
{
uint8_t x_358; 
x_358 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_282);
x_340 = x_349;
x_341 = x_351;
x_342 = x_354;
x_343 = x_358;
goto block_348;
}
}
block_384:
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
x_362 = l_Lean_IR_EmitC_toCType(x_286, x_360, x_361);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec_ref(x_362);
x_365 = lean_string_append(x_364, x_363);
lean_dec(x_363);
x_366 = l_Lean_IR_EmitC_emitSpreadArg___closed__0;
x_367 = lean_string_append(x_365, x_366);
x_368 = lean_unsigned_to_nat(0u);
x_369 = lean_array_get_size(x_285);
x_370 = lean_nat_dec_lt(x_368, x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_371 = l_Lean_IR_EmitC_toCInitName___closed__0;
x_372 = lean_string_append(x_371, x_337);
lean_dec(x_337);
x_373 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_374 = lean_string_append(x_372, x_373);
x_375 = lean_string_append(x_367, x_374);
lean_dec_ref(x_374);
x_319 = x_360;
x_320 = x_375;
goto block_329;
}
else
{
lean_object* x_376; 
x_376 = l_Lean_IR_EmitC_emitFnDeclAux___closed__2;
if (x_370 == 0)
{
x_349 = x_360;
x_350 = x_367;
x_351 = x_376;
goto block_359;
}
else
{
uint8_t x_377; 
x_377 = lean_nat_dec_le(x_369, x_369);
if (x_377 == 0)
{
if (x_370 == 0)
{
x_349 = x_360;
x_350 = x_367;
x_351 = x_376;
goto block_359;
}
else
{
size_t x_378; size_t x_379; lean_object* x_380; 
x_378 = 0;
x_379 = lean_usize_of_nat(x_369);
x_380 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_285, x_378, x_379, x_376);
x_349 = x_360;
x_350 = x_367;
x_351 = x_380;
goto block_359;
}
}
else
{
size_t x_381; size_t x_382; lean_object* x_383; 
x_381 = 0;
x_382 = lean_usize_of_nat(x_369);
x_383 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_285, x_381, x_382, x_376);
x_349 = x_360;
x_350 = x_367;
x_351 = x_383;
goto block_359;
}
}
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec_ref(x_335);
lean_dec(x_287);
lean_dec(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec(x_282);
x_392 = lean_ctor_get(x_336, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_336, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_394 = x_336;
} else {
 lean_dec_ref(x_336);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
block_311:
{
lean_object* x_290; 
x_290 = l_Lean_IR_EmitC_emitSpreads(x_285, x_288, x_289);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec_ref(x_290);
x_292 = lean_ctor_get(x_288, 0);
lean_inc_ref(x_292);
x_293 = lean_ctor_get(x_288, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_288, 2);
lean_inc_ref(x_294);
x_295 = lean_ctor_get(x_288, 5);
lean_inc_ref(x_295);
x_296 = lean_ctor_get(x_288, 6);
lean_inc_ref(x_296);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 lean_ctor_release(x_288, 4);
 lean_ctor_release(x_288, 5);
 lean_ctor_release(x_288, 6);
 x_297 = x_288;
} else {
 lean_dec_ref(x_288);
 x_297 = lean_box(0);
}
x_298 = l_Lean_IR_EmitC_emitDeclAux___closed__0;
x_299 = lean_string_append(x_291, x_298);
x_300 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_301 = lean_string_append(x_299, x_300);
if (lean_is_scalar(x_297)) {
 x_302 = lean_alloc_ctor(0, 7, 0);
} else {
 x_302 = x_297;
}
lean_ctor_set(x_302, 0, x_292);
lean_ctor_set(x_302, 1, x_293);
lean_ctor_set(x_302, 2, x_294);
lean_ctor_set(x_302, 3, x_284);
lean_ctor_set(x_302, 4, x_285);
lean_ctor_set(x_302, 5, x_295);
lean_ctor_set(x_302, 6, x_296);
x_303 = l_Lean_IR_EmitC_emitFnBody(x_287, x_302, x_301);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_305 = x_303;
} else {
 lean_dec_ref(x_303);
 x_305 = lean_box(0);
}
x_306 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_307 = lean_string_append(x_304, x_306);
x_308 = lean_box(0);
x_309 = lean_string_append(x_307, x_300);
if (lean_is_scalar(x_305)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_305;
}
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
else
{
return x_303;
}
}
else
{
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_285);
lean_dec(x_284);
return x_290;
}
}
block_318:
{
if (x_315 == 0)
{
lean_dec(x_314);
x_288 = x_312;
x_289 = x_313;
goto block_311;
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_inc(x_314);
x_316 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(x_285, x_314, x_314, x_313);
lean_dec(x_314);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec_ref(x_316);
x_288 = x_312;
x_289 = x_317;
goto block_311;
}
}
block_329:
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_321 = l_Lean_IR_EmitC_emitStructDefn___closed__0;
x_322 = lean_string_append(x_320, x_321);
x_323 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_324 = lean_string_append(x_322, x_323);
x_325 = l_Lean_closureMaxArgs;
x_326 = lean_array_get_size(x_285);
x_327 = lean_nat_dec_lt(x_325, x_326);
if (x_327 == 0)
{
lean_dec(x_282);
x_312 = x_319;
x_313 = x_324;
x_314 = x_326;
x_315 = x_327;
goto block_318;
}
else
{
uint8_t x_328; 
x_328 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_282);
lean_dec(x_282);
x_312 = x_319;
x_313 = x_324;
x_314 = x_326;
x_315 = x_328;
goto block_318;
}
}
block_334:
{
lean_object* x_332; lean_object* x_333; 
x_332 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1;
x_333 = lean_string_append(x_331, x_332);
x_319 = x_330;
x_320 = x_333;
goto block_329;
}
}
else
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec_ref(x_1);
x_396 = lean_box(0);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_3);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; 
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec_ref(x_1);
x_398 = lean_box(0);
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_3);
return x_399;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ncompiling:\n", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_IR_Decl_normalizeIds(x_1);
x_5 = l_Lean_IR_StructRC_visitDecl(x_4);
lean_inc_ref(x_5);
x_6 = l_Lean_IR_EmitC_emitDeclAux(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec_ref(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_IR_EmitC_emitDecl___closed__0;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_IR_declToString(x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = l_Lean_IR_EmitC_emitDecl___closed__0;
x_16 = lean_string_append(x_13, x_15);
x_17 = l_Lean_IR_declToString(x_5);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFns_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_8 = l_Lean_IR_EmitC_emitDecl(x_6, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFns(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = l_Lean_IR_getDecls(x_3);
x_5 = l_List_reverse___redArg(x_4);
x_6 = l_List_forM___at___00Lean_IR_EmitC_emitFns_spec__0(x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMarkPersistent___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_mark_persistent(", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_Decl_resultType(x_1);
x_6 = l_Lean_IR_IRType_isObj(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_IR_EmitC_emitMarkPersistent___closed__0;
x_10 = lean_string_append(x_4, x_9);
x_11 = l_Lean_IR_EmitC_emitCName(x_2, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_16 = lean_string_append(x_13, x_15);
x_17 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_18 = lean_box(0);
x_19 = lean_string_append(x_16, x_17);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lean_IR_EmitC_emitIncOfType___closed__0;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_24 = lean_box(0);
x_25 = lean_string_append(x_22, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(lean_box(0));", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (lean_io_result_is_error(res)) return res;", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = lean_io_result_get_value(res);", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(lean_io_result_get_value(res));", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (builtin) {", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("();", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_58; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_14);
lean_inc_ref(x_13);
x_58 = l_Lean_isIOUnitInitFn(x_13, x_14);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_59 = l_Lean_IR_Decl_params(x_1);
x_60 = lean_array_get_size(x_59);
lean_dec_ref(x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_14);
lean_dec_ref(x_2);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_3);
return x_71;
}
else
{
lean_object* x_72; 
lean_inc(x_14);
lean_inc_ref(x_13);
x_72 = lean_get_init_fn_name_for(x_13, x_14);
if (lean_obj_tag(x_72) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_105; lean_object* x_109; 
lean_inc_ref(x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
lean_inc(x_14);
lean_inc_ref(x_13);
x_109 = l_Lean_getBuiltinInitFnNameFor_x3f(x_13, x_14);
if (lean_obj_tag(x_109) == 0)
{
x_105 = x_58;
goto block_108;
}
else
{
lean_dec_ref(x_109);
x_105 = x_62;
goto block_108;
}
block_104:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = l_Lean_IR_EmitC_emitMainFn___closed__17;
x_77 = lean_string_append(x_75, x_76);
x_78 = l_Lean_IR_ExplicitBoxing_mkBoxedName(x_73);
lean_inc_ref(x_74);
x_79 = l_Lean_IR_EmitC_emitCName(x_78, x_74, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = l_Lean_IR_EmitC_emitDeclInit___closed__0;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_84 = lean_string_append(x_82, x_83);
x_85 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_86 = lean_string_append(x_84, x_85);
x_87 = lean_string_append(x_86, x_83);
lean_inc_ref(x_74);
lean_inc(x_14);
x_88 = l_Lean_IR_EmitC_emitCName(x_14, x_74, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = l_Lean_IR_Decl_resultType(x_1);
x_91 = l_Lean_IR_IRType_isScalarOrStruct(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_90);
x_92 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_93 = lean_string_append(x_89, x_92);
x_94 = lean_string_append(x_93, x_83);
lean_inc(x_14);
x_95 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_14, x_74, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_63 = x_96;
goto block_69;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
return x_95;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_98 = lean_string_append(x_89, x_97);
x_99 = l_Lean_IR_EmitC_emitUnboxFn(x_90, x_74, x_98);
lean_dec_ref(x_74);
lean_dec(x_90);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_string_append(x_102, x_83);
x_63 = x_103;
goto block_69;
}
}
else
{
lean_dec_ref(x_74);
lean_dec(x_14);
lean_dec_ref(x_13);
return x_88;
}
}
else
{
lean_dec_ref(x_74);
lean_dec(x_14);
lean_dec_ref(x_13);
return x_79;
}
}
block_108:
{
if (x_105 == 0)
{
x_74 = x_2;
x_75 = x_3;
goto block_104;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Lean_IR_EmitC_emitDeclInit___closed__4;
x_107 = lean_string_append(x_3, x_106);
x_74 = x_2;
x_75 = x_107;
goto block_104;
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_72);
lean_inc_ref(x_2);
lean_inc(x_14);
x_110 = l_Lean_IR_EmitC_emitCName(x_14, x_2, x_3);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1;
x_113 = lean_string_append(x_111, x_112);
lean_inc_ref(x_2);
lean_inc(x_14);
x_114 = l_Lean_IR_EmitC_emitCInitName(x_14, x_2, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l_Lean_IR_EmitC_emitDeclInit___closed__5;
x_117 = lean_string_append(x_115, x_116);
x_118 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_119 = lean_string_append(x_117, x_118);
x_120 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_14, x_2, x_119);
return x_120;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_2);
return x_114;
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_2);
return x_110;
}
}
}
block_69:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_65 = lean_string_append(x_63, x_64);
x_66 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_67 = lean_string_append(x_65, x_66);
x_68 = l_Lean_getBuiltinInitFnNameFor_x3f(x_13, x_14);
if (lean_obj_tag(x_68) == 0)
{
x_4 = x_67;
x_5 = x_58;
goto block_12;
}
else
{
lean_dec_ref(x_68);
x_4 = x_67;
x_5 = x_62;
goto block_12;
}
}
}
else
{
uint8_t x_121; 
lean_inc_ref(x_13);
lean_inc(x_14);
lean_inc_ref(x_13);
x_121 = l_Lean_isIOUnitBuiltinInitFn(x_13, x_14);
if (x_121 == 0)
{
x_15 = x_2;
x_16 = x_3;
goto block_57;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Lean_IR_EmitC_emitDeclInit___closed__4;
x_123 = lean_string_append(x_3, x_122);
x_15 = x_2;
x_16 = x_123;
goto block_57;
}
}
block_12:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_9 = lean_box(0);
x_10 = lean_string_append(x_4, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
block_57:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_IR_EmitC_emitMainFn___closed__17;
x_18 = lean_string_append(x_16, x_17);
lean_inc(x_14);
x_19 = l_Lean_IR_ExplicitBoxing_mkBoxedName(x_14);
x_20 = l_Lean_IR_EmitC_emitCName(x_19, x_15, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Lean_IR_EmitC_emitDeclInit___closed__0;
x_25 = lean_string_append(x_22, x_24);
x_26 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_26);
x_31 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_26);
x_34 = l_Lean_isIOUnitBuiltinInitFn(x_13, x_14);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
lean_ctor_set(x_20, 1, x_33);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_37 = lean_box(0);
x_38 = lean_string_append(x_33, x_36);
lean_ctor_set(x_20, 1, x_38);
lean_ctor_set(x_20, 0, x_37);
return x_20;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = l_Lean_IR_EmitC_emitDeclInit___closed__0;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_42);
x_47 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_42);
x_50 = l_Lean_isIOUnitBuiltinInitFn(x_13, x_14);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = l_Lean_IR_EmitC_emitSpreadValue___closed__1;
x_54 = lean_box(0);
x_55 = lean_string_append(x_49, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitDeclInit(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(builtin);", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_array_uget(x_2, x_3);
x_9 = l_Lean_IR_EmitC_emitMainFn___closed__17;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_14 = l_Lean_IR_EmitC_emitMainFn___closed__22;
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_17, x_6);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
else
{
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_uget(x_2, x_3);
x_10 = l_Lean_IR_EmitC_emitMainFn___closed__17;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___closed__0;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_15 = l_Lean_IR_EmitC_emitMainFn___closed__22;
lean_inc(x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_18, x_7);
lean_dec_ref(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg(x_1, x_2, x_23, x_4, x_20, x_21);
return x_24;
}
else
{
lean_dec(x_1);
return x_19;
}
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(uint8_t builtin);", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(internal) import without module index", 38, 38);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_4, x_3, x_12);
x_14 = l_Lean_Environment_getModulePackageByIdx_x3f(x_1, x_11);
lean_dec(x_11);
x_15 = l_Lean_mkModuleInitializationFunctionName(x_9, x_14);
lean_dec(x_14);
x_16 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0;
x_17 = lean_string_append(x_16, x_15);
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_5, x_19);
lean_dec_ref(x_19);
x_21 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_22 = lean_string_append(x_20, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_13, x_3, x_15);
x_3 = x_24;
x_4 = x_25;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_4);
x_27 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__1;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitInitFn_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_8 = l_Lean_IR_EmitC_emitDeclInit(x_6, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
else
{
lean_dec_ref(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitInitFn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitInitFn_spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("static bool _G_initialized = false;", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_EXPORT lean_object* ", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(uint8_t builtin) {", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_object * res;", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));", 61, 61);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_G_initialized = true;", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("return lean_io_result_mk_ok(lean_box(0));", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__36;
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__8;
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Environment_imports(x_3);
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg(x_3, x_6, x_7, x_5, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_32; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = lean_box(0);
lean_inc_ref(x_3);
x_16 = l_Lean_PersistentEnvExtension_getState___redArg(x_14, x_11, x_3, x_13, x_15);
lean_dec(x_13);
lean_inc(x_4);
x_17 = l_Lean_mkModuleInitializationFunctionName(x_4, x_16);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitInitFn___closed__0;
x_19 = l_Lean_IR_EmitC_emitInitFn___closed__1;
x_20 = lean_string_append(x_19, x_17);
lean_dec_ref(x_17);
x_21 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(0);
x_35 = l_Lean_IR_EmitC_emitInitFn___closed__10;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_37, x_10);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_array_get_size(x_9);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_dec(x_9);
x_24 = x_39;
goto block_31;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_box(0);
x_44 = lean_nat_dec_le(x_41, x_41);
if (x_44 == 0)
{
if (x_42 == 0)
{
lean_dec(x_9);
x_24 = x_39;
goto block_31;
}
else
{
size_t x_45; lean_object* x_46; 
x_45 = lean_usize_of_nat(x_41);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(x_23, x_9, x_7, x_45, x_43, x_1, x_39);
lean_dec(x_9);
x_32 = x_46;
goto block_34;
}
}
else
{
size_t x_47; lean_object* x_48; 
x_47 = lean_usize_of_nat(x_41);
x_48 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(x_23, x_9, x_7, x_47, x_43, x_1, x_39);
lean_dec(x_9);
x_32 = x_48;
goto block_34;
}
}
block_31:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_3);
x_25 = l_Lean_IR_getDecls(x_3);
x_26 = l_List_reverse___redArg(x_25);
x_27 = l_List_forM___at___00Lean_IR_EmitC_emitInitFn_spec__1(x_26, x_1, x_24);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_IR_EmitC_emitInitFn___closed__7;
x_30 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_29, x_28);
return x_30;
}
else
{
return x_27;
}
}
block_34:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_24 = x_33;
goto block_31;
}
else
{
lean_dec_ref(x_1);
return x_32;
}
}
}
else
{
uint8_t x_49; 
lean_dec_ref(x_1);
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
return x_8;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_main___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_Lean_IR_EmitC_emitFnDecls(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_5 = l_Lean_IR_EmitC_emitFns(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
lean_inc_ref(x_1);
x_7 = l_Lean_IR_EmitC_emitInitFn(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_EmitC_emitFileFooter___redArg(x_10);
return x_11;
}
else
{
return x_9;
}
}
else
{
lean_dec_ref(x_1);
return x_7;
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
}
else
{
lean_dec_ref(x_1);
return x_3;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_main___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_main___lam__0), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("void* memcpy(void* restrict, const void* restrict, size_t);", 59, 59);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_Lean_IR_EmitC_emitFileHeader(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_IR_EmitC_main___closed__0;
x_6 = l_Lean_IR_EmitC_main___closed__1;
x_7 = lean_string_append(x_4, x_6);
x_8 = l_Lean_IR_EmitC_emitLn___redArg___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitStructDecls___redArg(x_5, x_1, x_9);
return x_10;
}
else
{
lean_dec_ref(x_1);
return x_3;
}
}
}
static lean_object* _init_l_Lean_IR_emitC___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_emitC___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_emitC___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_emitC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_IR_emitC___closed__1;
x_4 = lean_box(0);
x_5 = l_Lean_IR_EmitC_emitFnDeclAux___closed__2;
x_6 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_3);
lean_ctor_set(x_6, 6, x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1;
x_8 = l_Lean_IR_EmitC_main(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_EmitUtil(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_SimpCase(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_StructRC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_SimpCase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Boxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_StructRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_EmitC_leanMainFn___closed__0 = _init_l_Lean_IR_EmitC_leanMainFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_leanMainFn___closed__0);
l_Lean_IR_EmitC_leanMainFn = _init_l_Lean_IR_EmitC_leanMainFn();
lean_mark_persistent(l_Lean_IR_EmitC_leanMainFn);
l_Lean_IR_EmitC_getDecl___closed__0 = _init_l_Lean_IR_EmitC_getDecl___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_getDecl___closed__0);
l_Lean_IR_EmitC_getDecl___closed__1 = _init_l_Lean_IR_EmitC_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_getDecl___closed__1);
l_Lean_IR_EmitC_emitLn___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitLn___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitLn___redArg___closed__0);
l_Lean_IR_EmitC_emitLns___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__0);
l_Lean_IR_EmitC_emitLns___redArg___closed__1 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__1);
l_Lean_IR_EmitC_emitLns___redArg___closed__2 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__2);
l_Lean_IR_EmitC_emitLns___redArg___closed__3 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__3);
l_Lean_IR_EmitC_emitLns___redArg___closed__4 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__4);
l_Lean_IR_EmitC_emitLns___redArg___closed__5 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__5);
l_Lean_IR_EmitC_emitLns___redArg___closed__6 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__6);
l_Lean_IR_EmitC_emitLns___redArg___closed__7 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__7);
l_Lean_IR_EmitC_emitLns___redArg___closed__8 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__8);
l_Lean_IR_EmitC_emitLns___redArg___closed__9 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__9);
l_Lean_IR_EmitC_emitLns___redArg___closed__10 = _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitLns___redArg___closed__10);
l_Lean_IR_EmitC_argToCString___closed__0 = _init_l_Lean_IR_EmitC_argToCString___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_argToCString___closed__0);
l_Lean_IR_EmitC_argToCString___closed__1 = _init_l_Lean_IR_EmitC_argToCString___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_argToCString___closed__1);
l_Lean_IR_EmitC_lookupStruct___closed__0 = _init_l_Lean_IR_EmitC_lookupStruct___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_lookupStruct___closed__0);
l_Lean_IR_EmitC_lookupStruct___closed__1 = _init_l_Lean_IR_EmitC_lookupStruct___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_lookupStruct___closed__1);
l_Lean_IR_EmitC_structType___closed__0 = _init_l_Lean_IR_EmitC_structType___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_structType___closed__0);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__0 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__0);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__1 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__1);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__2 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_EmitC_toCType_spec__0_spec__0___redArg___closed__3);
l_Lean_IR_EmitC_toCType___closed__0 = _init_l_Lean_IR_EmitC_toCType___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__0);
l_Lean_IR_EmitC_toCType___closed__1 = _init_l_Lean_IR_EmitC_toCType___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__1);
l_Lean_IR_EmitC_toCType___closed__2 = _init_l_Lean_IR_EmitC_toCType___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__2);
l_Lean_IR_EmitC_toCType___closed__3 = _init_l_Lean_IR_EmitC_toCType___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__3);
l_Lean_IR_EmitC_toCType___closed__4 = _init_l_Lean_IR_EmitC_toCType___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__4);
l_Lean_IR_EmitC_toCType___closed__5 = _init_l_Lean_IR_EmitC_toCType___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__5);
l_Lean_IR_EmitC_toCType___closed__6 = _init_l_Lean_IR_EmitC_toCType___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__6);
l_Lean_IR_EmitC_toCType___closed__7 = _init_l_Lean_IR_EmitC_toCType___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__7);
l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0 = _init_l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0);
l_Lean_IR_EmitC_toCName___closed__0 = _init_l_Lean_IR_EmitC_toCName___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__0);
l_Lean_IR_EmitC_toCName___closed__1 = _init_l_Lean_IR_EmitC_toCName___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__1);
l_Lean_IR_EmitC_toCInitName___closed__0 = _init_l_Lean_IR_EmitC_toCInitName___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_toCInitName___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadArg_spec__0___redArg___closed__0);
l_Lean_IR_EmitC_emitSpreadArg___closed__0 = _init_l_Lean_IR_EmitC_emitSpreadArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitSpreadArg___closed__0);
l_Lean_IR_EmitC_emitSpreadArg___closed__1 = _init_l_Lean_IR_EmitC_emitSpreadArg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitSpreadArg___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitSpreadValue_spec__0___redArg___lam__0___closed__1);
l_Lean_IR_EmitC_emitSpreadValue___closed__0 = _init_l_Lean_IR_EmitC_emitSpreadValue___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitSpreadValue___closed__0);
l_Lean_IR_EmitC_emitSpreadValue___closed__1 = _init_l_Lean_IR_EmitC_emitSpreadValue___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitSpreadValue___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_EmitC_emitSpreads_spec__0___closed__2);
l_Lean_IR_EmitC_emitFnDeclAux___closed__0 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__0);
l_Lean_IR_EmitC_emitFnDeclAux___closed__1 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__1);
l_Lean_IR_EmitC_emitFnDeclAux___closed__2 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__2);
l_Lean_IR_EmitC_emitFnDeclAux___closed__3 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__3);
l_Lean_IR_EmitC_emitFnDeclAux___closed__4 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__4);
l_Lean_IR_EmitC_emitFnDeclAux___closed__5 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__5);
l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__0 = _init_l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__0();
lean_mark_persistent(l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__0);
l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__1 = _init_l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__1();
lean_mark_persistent(l_List_forM___at___00Lean_IR_EmitC_emitFnDecls_spec__3___closed__1);
l_Lean_IR_EmitC_emitMainFn___closed__0 = _init_l_Lean_IR_EmitC_emitMainFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__0);
l_Lean_IR_EmitC_emitMainFn___closed__1 = _init_l_Lean_IR_EmitC_emitMainFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__1);
l_Lean_IR_EmitC_emitMainFn___closed__2 = _init_l_Lean_IR_EmitC_emitMainFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__2);
l_Lean_IR_EmitC_emitMainFn___closed__3 = _init_l_Lean_IR_EmitC_emitMainFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__3);
l_Lean_IR_EmitC_emitMainFn___closed__4 = _init_l_Lean_IR_EmitC_emitMainFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__4);
l_Lean_IR_EmitC_emitMainFn___closed__5 = _init_l_Lean_IR_EmitC_emitMainFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__5);
l_Lean_IR_EmitC_emitMainFn___closed__6 = _init_l_Lean_IR_EmitC_emitMainFn___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__6);
l_Lean_IR_EmitC_emitMainFn___closed__7 = _init_l_Lean_IR_EmitC_emitMainFn___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__7);
l_Lean_IR_EmitC_emitMainFn___closed__8 = _init_l_Lean_IR_EmitC_emitMainFn___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__8);
l_Lean_IR_EmitC_emitMainFn___closed__9 = _init_l_Lean_IR_EmitC_emitMainFn___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__9);
l_Lean_IR_EmitC_emitMainFn___closed__10 = _init_l_Lean_IR_EmitC_emitMainFn___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__10);
l_Lean_IR_EmitC_emitMainFn___closed__11 = _init_l_Lean_IR_EmitC_emitMainFn___closed__11();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__11);
l_Lean_IR_EmitC_emitMainFn___closed__12 = _init_l_Lean_IR_EmitC_emitMainFn___closed__12();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__12);
l_Lean_IR_EmitC_emitMainFn___closed__13 = _init_l_Lean_IR_EmitC_emitMainFn___closed__13();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__13);
l_Lean_IR_EmitC_emitMainFn___closed__14 = _init_l_Lean_IR_EmitC_emitMainFn___closed__14();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__14);
l_Lean_IR_EmitC_emitMainFn___closed__15 = _init_l_Lean_IR_EmitC_emitMainFn___closed__15();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__15);
l_Lean_IR_EmitC_emitMainFn___closed__16 = _init_l_Lean_IR_EmitC_emitMainFn___closed__16();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__16);
l_Lean_IR_EmitC_emitMainFn___closed__17 = _init_l_Lean_IR_EmitC_emitMainFn___closed__17();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__17);
l_Lean_IR_EmitC_emitMainFn___closed__18 = _init_l_Lean_IR_EmitC_emitMainFn___closed__18();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__18);
l_Lean_IR_EmitC_emitMainFn___closed__19 = _init_l_Lean_IR_EmitC_emitMainFn___closed__19();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__19);
l_Lean_IR_EmitC_emitMainFn___closed__20 = _init_l_Lean_IR_EmitC_emitMainFn___closed__20();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__20);
l_Lean_IR_EmitC_emitMainFn___closed__21 = _init_l_Lean_IR_EmitC_emitMainFn___closed__21();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__21);
l_Lean_IR_EmitC_emitMainFn___closed__22 = _init_l_Lean_IR_EmitC_emitMainFn___closed__22();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__22);
l_Lean_IR_EmitC_emitMainFn___closed__23 = _init_l_Lean_IR_EmitC_emitMainFn___closed__23();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__23);
l_Lean_IR_EmitC_emitMainFn___closed__24 = _init_l_Lean_IR_EmitC_emitMainFn___closed__24();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__24);
l_Lean_IR_EmitC_emitMainFn___closed__25 = _init_l_Lean_IR_EmitC_emitMainFn___closed__25();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__25);
l_Lean_IR_EmitC_emitMainFn___closed__26 = _init_l_Lean_IR_EmitC_emitMainFn___closed__26();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__26);
l_Lean_IR_EmitC_emitMainFn___closed__27 = _init_l_Lean_IR_EmitC_emitMainFn___closed__27();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__27);
l_Lean_IR_EmitC_emitMainFn___closed__28 = _init_l_Lean_IR_EmitC_emitMainFn___closed__28();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__28);
l_Lean_IR_EmitC_emitMainFn___closed__29 = _init_l_Lean_IR_EmitC_emitMainFn___closed__29();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__29);
l_Lean_IR_EmitC_emitMainFn___closed__30 = _init_l_Lean_IR_EmitC_emitMainFn___closed__30();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__30);
l_Lean_IR_EmitC_emitMainFn___closed__31 = _init_l_Lean_IR_EmitC_emitMainFn___closed__31();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__31);
l_Lean_IR_EmitC_emitMainFn___closed__32 = _init_l_Lean_IR_EmitC_emitMainFn___closed__32();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__32);
l_Lean_IR_EmitC_emitMainFn___closed__33 = _init_l_Lean_IR_EmitC_emitMainFn___closed__33();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__33);
l_Lean_IR_EmitC_emitMainFn___closed__34 = _init_l_Lean_IR_EmitC_emitMainFn___closed__34();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__34);
l_Lean_IR_EmitC_emitMainFn___closed__35 = _init_l_Lean_IR_EmitC_emitMainFn___closed__35();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__35);
l_Lean_IR_EmitC_emitMainFn___closed__36 = _init_l_Lean_IR_EmitC_emitMainFn___closed__36();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__36);
l_Lean_IR_EmitC_emitMainFn___closed__37 = _init_l_Lean_IR_EmitC_emitMainFn___closed__37();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__37);
l_Lean_IR_EmitC_emitMainFn___closed__38 = _init_l_Lean_IR_EmitC_emitMainFn___closed__38();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__38);
l_Lean_IR_EmitC_emitMainFn___closed__39 = _init_l_Lean_IR_EmitC_emitMainFn___closed__39();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__39);
l_Lean_IR_EmitC_emitMainFn___closed__40 = _init_l_Lean_IR_EmitC_emitMainFn___closed__40();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__40);
l_Lean_IR_EmitC_emitMainFn___closed__41 = _init_l_Lean_IR_EmitC_emitMainFn___closed__41();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__41);
l_Lean_IR_EmitC_emitMainFn___closed__42 = _init_l_Lean_IR_EmitC_emitMainFn___closed__42();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__42);
l_Lean_IR_EmitC_emitMainFn___closed__43 = _init_l_Lean_IR_EmitC_emitMainFn___closed__43();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__43);
l_Lean_IR_EmitC_emitMainFn___closed__44 = _init_l_Lean_IR_EmitC_emitMainFn___closed__44();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__44);
l_Lean_IR_EmitC_emitMainFn___closed__45 = _init_l_Lean_IR_EmitC_emitMainFn___closed__45();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__45);
l_Lean_IR_EmitC_emitMainFn___closed__46 = _init_l_Lean_IR_EmitC_emitMainFn___closed__46();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__46);
l_Lean_IR_EmitC_emitMainFn___closed__47 = _init_l_Lean_IR_EmitC_emitMainFn___closed__47();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__47);
l_Lean_IR_EmitC_emitMainFn___closed__48 = _init_l_Lean_IR_EmitC_emitMainFn___closed__48();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__48);
l_Lean_IR_EmitC_emitMainFn___closed__49 = _init_l_Lean_IR_EmitC_emitMainFn___closed__49();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__49);
l_Lean_IR_EmitC_emitMainFn___closed__50 = _init_l_Lean_IR_EmitC_emitMainFn___closed__50();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__50);
l_Lean_IR_EmitC_emitMainFn___closed__51 = _init_l_Lean_IR_EmitC_emitMainFn___closed__51();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__51);
l_Lean_IR_EmitC_emitMainFn___closed__52 = _init_l_Lean_IR_EmitC_emitMainFn___closed__52();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__52);
l_Lean_IR_EmitC_emitMainFn___closed__53 = _init_l_Lean_IR_EmitC_emitMainFn___closed__53();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__53);
l_Lean_IR_EmitC_emitMainFn___closed__54 = _init_l_Lean_IR_EmitC_emitMainFn___closed__54();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__54);
l_Lean_IR_EmitC_emitMainFn___closed__55 = _init_l_Lean_IR_EmitC_emitMainFn___closed__55();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__55);
l_Lean_IR_EmitC_hasMainFn___closed__0 = _init_l_Lean_IR_EmitC_hasMainFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_hasMainFn___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__4 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__4();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__4);
l_Lean_IR_EmitC_emitFileHeader___closed__0 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__0);
l_Lean_IR_EmitC_emitFileHeader___closed__1 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__1);
l_Lean_IR_EmitC_emitFileHeader___closed__2 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__2);
l_Lean_IR_EmitC_emitFileHeader___closed__3 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__3);
l_Lean_IR_EmitC_emitFileHeader___closed__4 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__4);
l_Lean_IR_EmitC_emitFileHeader___closed__5 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__5);
l_Lean_IR_EmitC_emitFileHeader___closed__6 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__6);
l_Lean_IR_EmitC_emitFileHeader___closed__7 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__7);
l_Lean_IR_EmitC_emitFileHeader___closed__8 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__8);
l_Lean_IR_EmitC_emitFileHeader___closed__9 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__9);
l_Lean_IR_EmitC_emitFileHeader___closed__10 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__10);
l_Lean_IR_EmitC_emitFileHeader___closed__11 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__11();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__11);
l_Lean_IR_EmitC_emitFileHeader___closed__12 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__12();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__12);
l_Lean_IR_EmitC_emitFileHeader___closed__13 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__13();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__13);
l_Lean_IR_EmitC_emitFileHeader___closed__14 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__14();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__14);
l_Lean_IR_EmitC_emitFileHeader___closed__15 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__15();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__15);
l_Lean_IR_EmitC_emitFileHeader___closed__16 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__16();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__16);
l_Lean_IR_EmitC_emitFileHeader___closed__17 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__17();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__17);
l_Lean_IR_EmitC_emitFileHeader___closed__18 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__18();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__18);
l_Lean_IR_EmitC_emitFileHeader___closed__19 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__19();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__19);
l_Lean_IR_EmitC_emitFileHeader___closed__20 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__20();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__20);
l_Lean_IR_EmitC_emitFileHeader___closed__21 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__21();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__21);
l_Lean_IR_EmitC_emitFileHeader___closed__22 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__22();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__22);
l_Lean_IR_EmitC_emitFileHeader___closed__23 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__23();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__23);
l_Lean_IR_EmitC_emitFileHeader___closed__24 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__24();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__24);
l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0);
l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1 = _init_l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1);
l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0 = _init_l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0);
l_Lean_IR_EmitC_getJPParams___closed__0 = _init_l_Lean_IR_EmitC_getJPParams___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_getJPParams___closed__0);
l_Lean_IR_EmitC_declareVar___closed__0 = _init_l_Lean_IR_EmitC_declareVar___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_declareVar___closed__0);
l_Lean_IR_EmitC_optionLikePath___closed__0 = _init_l_Lean_IR_EmitC_optionLikePath___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_optionLikePath___closed__0);
l_Lean_IR_EmitC_optionLikePath___closed__1 = _init_l_Lean_IR_EmitC_optionLikePath___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_optionLikePath___closed__1);
l_Lean_IR_EmitC_emitPath___closed__0 = _init_l_Lean_IR_EmitC_emitPath___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitPath___closed__0);
l_Lean_IR_EmitC_emitTag___closed__0 = _init_l_Lean_IR_EmitC_emitTag___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitTag___closed__0);
l_Lean_IR_EmitC_emitTag___closed__1 = _init_l_Lean_IR_EmitC_emitTag___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitTag___closed__1);
l_Lean_IR_EmitC_emitTag___closed__2 = _init_l_Lean_IR_EmitC_emitTag___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitTag___closed__2);
l_Lean_IR_EmitC_structIncFnPrefix___closed__0 = _init_l_Lean_IR_EmitC_structIncFnPrefix___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_structIncFnPrefix___closed__0);
l_Lean_IR_EmitC_structIncFnPrefix = _init_l_Lean_IR_EmitC_structIncFnPrefix();
lean_mark_persistent(l_Lean_IR_EmitC_structIncFnPrefix);
l_Lean_IR_EmitC_structDecFnPrefix___closed__0 = _init_l_Lean_IR_EmitC_structDecFnPrefix___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_structDecFnPrefix___closed__0);
l_Lean_IR_EmitC_structDecFnPrefix = _init_l_Lean_IR_EmitC_structDecFnPrefix();
lean_mark_persistent(l_Lean_IR_EmitC_structDecFnPrefix);
l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0 = _init_l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_structReshapeFnPrefix___closed__0);
l_Lean_IR_EmitC_structReshapeFnPrefix = _init_l_Lean_IR_EmitC_structReshapeFnPrefix();
lean_mark_persistent(l_Lean_IR_EmitC_structReshapeFnPrefix);
l_Lean_IR_EmitC_structBoxFnPrefix___closed__0 = _init_l_Lean_IR_EmitC_structBoxFnPrefix___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_structBoxFnPrefix___closed__0);
l_Lean_IR_EmitC_structBoxFnPrefix = _init_l_Lean_IR_EmitC_structBoxFnPrefix();
lean_mark_persistent(l_Lean_IR_EmitC_structBoxFnPrefix);
l_Lean_IR_EmitC_structUnboxFnPrefix___closed__0 = _init_l_Lean_IR_EmitC_structUnboxFnPrefix___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_structUnboxFnPrefix___closed__0);
l_Lean_IR_EmitC_structUnboxFnPrefix = _init_l_Lean_IR_EmitC_structUnboxFnPrefix();
lean_mark_persistent(l_Lean_IR_EmitC_structUnboxFnPrefix);
l_Lean_IR_EmitC_emitIncOfType___closed__0 = _init_l_Lean_IR_EmitC_emitIncOfType___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitIncOfType___closed__0);
l_Lean_IR_EmitC_emitIncOfType___closed__1 = _init_l_Lean_IR_EmitC_emitIncOfType___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitIncOfType___closed__1);
l_Lean_IR_EmitC_emitIncOfType___closed__2 = _init_l_Lean_IR_EmitC_emitIncOfType___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitIncOfType___closed__2);
l_Lean_IR_EmitC_emitIncOfType___closed__3 = _init_l_Lean_IR_EmitC_emitIncOfType___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitIncOfType___closed__3);
l_Lean_IR_EmitC_emitIncOfType___closed__4 = _init_l_Lean_IR_EmitC_emitIncOfType___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitIncOfType___closed__4);
l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__0 = _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__0);
l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__1 = _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDecOfType_spec__0___redArg___closed__1);
l_Lean_IR_EmitC_emitDel___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitDel___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitDel___redArg___closed__0);
l_Lean_IR_EmitC_emitSetTag___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitSetTag___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitSetTag___redArg___closed__0);
l_Lean_IR_EmitC_emitSet___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitSet___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitSet___redArg___closed__0);
l_Lean_IR_EmitC_emitOffset___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitOffset___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitOffset___redArg___closed__0);
l_Lean_IR_EmitC_emitOffset___redArg___closed__1 = _init_l_Lean_IR_EmitC_emitOffset___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitOffset___redArg___closed__1);
l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0___closed__0 = _init_l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_IR_EmitC_emitUSet_spec__0___closed__0);
l_Lean_IR_EmitC_emitUSet___closed__0 = _init_l_Lean_IR_EmitC_emitUSet___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__0);
l_Lean_IR_EmitC_emitUSet___closed__1 = _init_l_Lean_IR_EmitC_emitUSet___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__1);
l_Lean_IR_EmitC_emitUSet___closed__2 = _init_l_Lean_IR_EmitC_emitUSet___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__2);
l_Lean_IR_EmitC_emitUSet___closed__3 = _init_l_Lean_IR_EmitC_emitUSet___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__3);
l_Lean_IR_EmitC_emitUSet___closed__4 = _init_l_Lean_IR_EmitC_emitUSet___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__4);
l_Lean_IR_EmitC_emitUSet___closed__5 = _init_l_Lean_IR_EmitC_emitUSet___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__5);
l_Lean_IR_EmitC_emitUSet___closed__6 = _init_l_Lean_IR_EmitC_emitUSet___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__6);
l_Lean_IR_EmitC_emitUSet___closed__7 = _init_l_Lean_IR_EmitC_emitUSet___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__7);
l_Lean_IR_EmitC_emitSSet___closed__0 = _init_l_Lean_IR_EmitC_emitSSet___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__0);
l_Lean_IR_EmitC_emitSSet___closed__1 = _init_l_Lean_IR_EmitC_emitSSet___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__1);
l_Lean_IR_EmitC_emitSSet___closed__2 = _init_l_Lean_IR_EmitC_emitSSet___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__2);
l_Lean_IR_EmitC_emitSSet___closed__3 = _init_l_Lean_IR_EmitC_emitSSet___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__3);
l_Lean_IR_EmitC_emitSSet___closed__4 = _init_l_Lean_IR_EmitC_emitSSet___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__4);
l_Lean_IR_EmitC_emitSSet___closed__5 = _init_l_Lean_IR_EmitC_emitSSet___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__5);
l_Lean_IR_EmitC_emitSSet___closed__6 = _init_l_Lean_IR_EmitC_emitSSet___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__6);
l_Lean_IR_EmitC_emitSSet___closed__7 = _init_l_Lean_IR_EmitC_emitSSet___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__7);
l_Lean_IR_EmitC_emitSSet___closed__8 = _init_l_Lean_IR_EmitC_emitSSet___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__8);
l_Lean_IR_EmitC_emitSSet___closed__9 = _init_l_Lean_IR_EmitC_emitSSet___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__9);
l_Lean_IR_EmitC_emitSSet___closed__10 = _init_l_Lean_IR_EmitC_emitSSet___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__10);
l_Lean_IR_EmitC_emitJmp___closed__0 = _init_l_Lean_IR_EmitC_emitJmp___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitJmp___closed__0);
l_Lean_IR_EmitC_emitJmp___closed__1 = _init_l_Lean_IR_EmitC_emitJmp___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitJmp___closed__1);
l_Lean_IR_EmitC_emitJmp___closed__2 = _init_l_Lean_IR_EmitC_emitJmp___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitJmp___closed__2);
l_Lean_IR_EmitC_emitCtorScalarSize___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitCtorScalarSize___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtorScalarSize___redArg___closed__0);
l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0);
l_Lean_IR_EmitC_emitCtor___closed__0 = _init_l_Lean_IR_EmitC_emitCtor___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtor___closed__0);
l_Lean_IR_EmitC_emitCtor___closed__1 = _init_l_Lean_IR_EmitC_emitCtor___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtor___closed__1);
l_Lean_IR_EmitC_emitCtor___closed__2 = _init_l_Lean_IR_EmitC_emitCtor___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtor___closed__2);
l_Lean_IR_EmitC_emitCtor___closed__3 = _init_l_Lean_IR_EmitC_emitCtor___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtor___closed__3);
l_Lean_IR_EmitC_emitCtor___closed__4 = _init_l_Lean_IR_EmitC_emitCtor___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtor___closed__4);
l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0 = _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0);
l_Lean_IR_EmitC_emitReset___closed__0 = _init_l_Lean_IR_EmitC_emitReset___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitReset___closed__0);
l_Lean_IR_EmitC_emitReset___closed__1 = _init_l_Lean_IR_EmitC_emitReset___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitReset___closed__1);
l_Lean_IR_EmitC_emitReset___closed__2 = _init_l_Lean_IR_EmitC_emitReset___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitReset___closed__2);
l_Lean_IR_EmitC_emitReset___closed__3 = _init_l_Lean_IR_EmitC_emitReset___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitReset___closed__3);
l_Lean_IR_EmitC_emitReuse___closed__0 = _init_l_Lean_IR_EmitC_emitReuse___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitReuse___closed__0);
l_Lean_IR_EmitC_emitReuse___closed__1 = _init_l_Lean_IR_EmitC_emitReuse___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitReuse___closed__1);
l_Lean_IR_EmitC_emitProj___closed__0 = _init_l_Lean_IR_EmitC_emitProj___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitProj___closed__0);
l_Lean_IR_EmitC_emitUProj___closed__0 = _init_l_Lean_IR_EmitC_emitUProj___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitUProj___closed__0);
l_Lean_IR_EmitC_emitUProj___closed__1 = _init_l_Lean_IR_EmitC_emitUProj___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitUProj___closed__1);
l_Lean_IR_EmitC_emitUProj___closed__2 = _init_l_Lean_IR_EmitC_emitUProj___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitUProj___closed__2);
l_Lean_IR_EmitC_emitUProj___closed__3 = _init_l_Lean_IR_EmitC_emitUProj___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitUProj___closed__3);
l_Lean_IR_EmitC_emitSProj___closed__0 = _init_l_Lean_IR_EmitC_emitSProj___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__0);
l_Lean_IR_EmitC_emitSProj___closed__1 = _init_l_Lean_IR_EmitC_emitSProj___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__1);
l_Lean_IR_EmitC_emitSProj___closed__2 = _init_l_Lean_IR_EmitC_emitSProj___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__2);
l_Lean_IR_EmitC_emitSProj___closed__3 = _init_l_Lean_IR_EmitC_emitSProj___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__3);
l_Lean_IR_EmitC_emitSProj___closed__4 = _init_l_Lean_IR_EmitC_emitSProj___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__4);
l_Lean_IR_EmitC_emitSProj___closed__5 = _init_l_Lean_IR_EmitC_emitSProj___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__5);
l_Lean_IR_EmitC_emitSProj___closed__6 = _init_l_Lean_IR_EmitC_emitSProj___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__6);
l_Lean_IR_EmitC_emitExternCall___closed__0 = _init_l_Lean_IR_EmitC_emitExternCall___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitExternCall___closed__0);
l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0 = _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0);
l_Lean_IR_EmitC_emitPartialApp___closed__0 = _init_l_Lean_IR_EmitC_emitPartialApp___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitPartialApp___closed__0);
l_Lean_IR_EmitC_emitPartialApp___closed__1 = _init_l_Lean_IR_EmitC_emitPartialApp___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitPartialApp___closed__1);
l_Lean_IR_EmitC_emitApp___closed__0 = _init_l_Lean_IR_EmitC_emitApp___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__0);
l_Lean_IR_EmitC_emitApp___closed__1 = _init_l_Lean_IR_EmitC_emitApp___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__1);
l_Lean_IR_EmitC_emitApp___closed__2 = _init_l_Lean_IR_EmitC_emitApp___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__2);
l_Lean_IR_EmitC_emitApp___closed__3 = _init_l_Lean_IR_EmitC_emitApp___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__3);
l_Lean_IR_EmitC_emitApp___closed__4 = _init_l_Lean_IR_EmitC_emitApp___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__4);
l_Lean_IR_EmitC_emitBoxFn___closed__0 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__0);
l_Lean_IR_EmitC_emitBoxFn___closed__1 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__1);
l_Lean_IR_EmitC_emitBoxFn___closed__2 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__2);
l_Lean_IR_EmitC_emitBoxFn___closed__3 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__3);
l_Lean_IR_EmitC_emitBoxFn___closed__4 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__4);
l_Lean_IR_EmitC_emitBoxFn___closed__5 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__5);
l_Lean_IR_EmitC_emitIsShared___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitIsShared___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitIsShared___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6);
l_Lean_IR_EmitC_quoteString___closed__0 = _init_l_Lean_IR_EmitC_quoteString___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___closed__0);
l_Lean_IR_EmitC_emitNumLit___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___redArg___closed__0);
l_Lean_IR_EmitC_emitNumLit___redArg___closed__1 = _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___redArg___closed__1);
l_Lean_IR_EmitC_emitNumLit___redArg___closed__2 = _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___redArg___closed__2);
l_Lean_IR_EmitC_emitNumLit___redArg___closed__3 = _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___redArg___closed__3);
l_Lean_IR_EmitC_emitNumLit___redArg___closed__4 = _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___redArg___closed__4);
l_Lean_IR_EmitC_emitNumLit___redArg___closed__5 = _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___redArg___closed__5);
l_Lean_IR_EmitC_emitNumLit___redArg___closed__6 = _init_l_Lean_IR_EmitC_emitNumLit___redArg___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___redArg___closed__6);
l_Lean_IR_EmitC_emitLit___redArg___closed__0 = _init_l_Lean_IR_EmitC_emitLit___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitLit___redArg___closed__0);
l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0 = _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0);
l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0 = _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0);
l_Lean_IR_EmitC_emitTailCall___closed__0 = _init_l_Lean_IR_EmitC_emitTailCall___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__0);
l_Lean_IR_EmitC_emitTailCall___closed__1 = _init_l_Lean_IR_EmitC_emitTailCall___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__1);
l_Lean_IR_EmitC_emitTailCall___closed__2 = _init_l_Lean_IR_EmitC_emitTailCall___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__2);
l_Lean_IR_EmitC_emitTailCall___closed__3 = _init_l_Lean_IR_EmitC_emitTailCall___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__3);
l_Lean_IR_EmitC_emitIf___closed__0 = _init_l_Lean_IR_EmitC_emitIf___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__0);
l_Lean_IR_EmitC_emitIf___closed__1 = _init_l_Lean_IR_EmitC_emitIf___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__1);
l_Lean_IR_EmitC_emitIf___closed__2 = _init_l_Lean_IR_EmitC_emitIf___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__2);
l_Lean_IR_EmitC_emitCase___closed__0 = _init_l_Lean_IR_EmitC_emitCase___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitCase___closed__0);
l_Lean_IR_EmitC_emitCase___closed__1 = _init_l_Lean_IR_EmitC_emitCase___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitCase___closed__1);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0);
l_Lean_IR_EmitC_emitJPs___closed__0 = _init_l_Lean_IR_EmitC_emitJPs___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitJPs___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1);
l_Lean_IR_EmitC_emitBlock___closed__0 = _init_l_Lean_IR_EmitC_emitBlock___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitBlock___closed__0);
l_Lean_IR_EmitC_emitBlock___closed__1 = _init_l_Lean_IR_EmitC_emitBlock___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitBlock___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__0___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructDefn_spec__1___redArg___closed__0);
l_Lean_IR_EmitC_emitStructDefn___closed__0 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__0);
l_Lean_IR_EmitC_emitStructDefn___closed__1 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__1);
l_Lean_IR_EmitC_emitStructDefn___closed__2 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__2);
l_Lean_IR_EmitC_emitStructDefn___closed__3 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__3);
l_Lean_IR_EmitC_emitStructDefn___closed__4 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__4);
l_Lean_IR_EmitC_emitStructDefn___closed__5 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__5);
l_Lean_IR_EmitC_emitStructDefn___closed__6 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__6);
l_Lean_IR_EmitC_emitStructDefn___closed__7 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__7);
l_Lean_IR_EmitC_emitStructDefn___closed__8 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__8);
l_Lean_IR_EmitC_emitStructDefn___closed__9 = _init_l_Lean_IR_EmitC_emitStructDefn___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructDefn___closed__9);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitUnionSwitch_spec__0___redArg___closed__0);
l_Lean_IR_EmitC_emitUnionSwitch___closed__0 = _init_l_Lean_IR_EmitC_emitUnionSwitch___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnionSwitch___closed__0);
l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__0 = _init_l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__0);
l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__1 = _init_l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnionSwitchWithImpossible___closed__1);
l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___closed__0 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___lam__0___closed__0);
l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___closed__0 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___lam__1___closed__0);
l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructIncDecFn_spec__0_spec__0___redArg___closed__0);
l_Lean_IR_EmitC_emitStructIncDecFn___closed__0 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___closed__0);
l_Lean_IR_EmitC_emitStructIncDecFn___closed__1 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___closed__1);
l_Lean_IR_EmitC_emitStructIncDecFn___closed__2 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___closed__2);
l_Lean_IR_EmitC_emitStructIncDecFn___closed__3 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___closed__3);
l_Lean_IR_EmitC_emitStructIncDecFn___closed__4 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___closed__4);
l_Lean_IR_EmitC_emitStructIncDecFn___closed__5 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___closed__5);
l_Lean_IR_EmitC_emitStructIncDecFn___closed__6 = _init_l_Lean_IR_EmitC_emitStructIncDecFn___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructIncDecFn___closed__6);
l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__0 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__0);
l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__1 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___lam__0___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___lam__0___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__2 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__2();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__2);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__3 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__3();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__3);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__4 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__4();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructReshapeFn_spec__0___redArg___closed__4);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__0 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__0);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__1 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__1);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__2 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__2);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__3 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__3);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__4 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__4);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__5 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__5);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__6 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__6);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__7 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__7);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__8 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__8);
l_Lean_IR_EmitC_emitStructReshapeFn___closed__9 = _init_l_Lean_IR_EmitC_emitStructReshapeFn___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructReshapeFn___closed__9);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructBox_spec__0___redArg___closed__1);
l_Lean_IR_EmitC_emitStructBox___closed__0 = _init_l_Lean_IR_EmitC_emitStructBox___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBox___closed__0);
l_Lean_IR_EmitC_emitStructBox___closed__1 = _init_l_Lean_IR_EmitC_emitStructBox___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBox___closed__1);
l_Lean_IR_EmitC_emitStructBox___closed__2 = _init_l_Lean_IR_EmitC_emitStructBox___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBox___closed__2);
l_Lean_IR_EmitC_emitStructBox___closed__3 = _init_l_Lean_IR_EmitC_emitStructBox___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBox___closed__3);
l_Lean_IR_EmitC_emitStructBox___closed__4 = _init_l_Lean_IR_EmitC_emitStructBox___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBox___closed__4);
l_Lean_IR_EmitC_emitStructBox___closed__5 = _init_l_Lean_IR_EmitC_emitStructBox___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBox___closed__5);
l_Lean_IR_EmitC_emitStructBox___closed__6 = _init_l_Lean_IR_EmitC_emitStructBox___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBox___closed__6);
l_Lean_IR_EmitC_emitStructBoxFn___closed__0 = _init_l_Lean_IR_EmitC_emitStructBoxFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBoxFn___closed__0);
l_Lean_IR_EmitC_emitStructBoxFn___closed__1 = _init_l_Lean_IR_EmitC_emitStructBoxFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBoxFn___closed__1);
l_Lean_IR_EmitC_emitStructBoxFn___closed__2 = _init_l_Lean_IR_EmitC_emitStructBoxFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBoxFn___closed__2);
l_Lean_IR_EmitC_emitStructBoxFn___closed__3 = _init_l_Lean_IR_EmitC_emitStructBoxFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructBoxFn___closed__3);
l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___closed__0 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___lam__0___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_emitStructUnboxFn_spec__0___redArg___closed__1);
l_Lean_IR_EmitC_emitStructUnboxFn___closed__0 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___closed__0);
l_Lean_IR_EmitC_emitStructUnboxFn___closed__1 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___closed__1);
l_Lean_IR_EmitC_emitStructUnboxFn___closed__2 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___closed__2);
l_Lean_IR_EmitC_emitStructUnboxFn___closed__3 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___closed__3);
l_Lean_IR_EmitC_emitStructUnboxFn___closed__4 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___closed__4);
l_Lean_IR_EmitC_emitStructUnboxFn___closed__5 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___closed__5);
l_Lean_IR_EmitC_emitStructUnboxFn___closed__6 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___closed__6);
l_Lean_IR_EmitC_emitStructUnboxFn___closed__7 = _init_l_Lean_IR_EmitC_emitStructUnboxFn___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitStructUnboxFn___closed__7);
l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0 = _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0);
l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1 = _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1);
l_Lean_IR_EmitC_emitDeclAux___closed__0 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__0);
l_Lean_IR_EmitC_emitDeclAux___closed__1 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__1);
l_Lean_IR_EmitC_emitDeclAux___closed__2 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__2);
l_Lean_IR_EmitC_emitDecl___closed__0 = _init_l_Lean_IR_EmitC_emitDecl___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitDecl___closed__0);
l_Lean_IR_EmitC_emitMarkPersistent___closed__0 = _init_l_Lean_IR_EmitC_emitMarkPersistent___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitMarkPersistent___closed__0);
l_Lean_IR_EmitC_emitDeclInit___closed__0 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__0);
l_Lean_IR_EmitC_emitDeclInit___closed__1 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__1);
l_Lean_IR_EmitC_emitDeclInit___closed__2 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__2);
l_Lean_IR_EmitC_emitDeclInit___closed__3 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__3);
l_Lean_IR_EmitC_emitDeclInit___closed__4 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__4);
l_Lean_IR_EmitC_emitDeclInit___closed__5 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__5);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2_spec__2___redArg___closed__0);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__0);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_EmitC_emitInitFn_spec__0___redArg___closed__1);
l_Lean_IR_EmitC_emitInitFn___closed__0 = _init_l_Lean_IR_EmitC_emitInitFn___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__0);
l_Lean_IR_EmitC_emitInitFn___closed__1 = _init_l_Lean_IR_EmitC_emitInitFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__1);
l_Lean_IR_EmitC_emitInitFn___closed__2 = _init_l_Lean_IR_EmitC_emitInitFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__2);
l_Lean_IR_EmitC_emitInitFn___closed__3 = _init_l_Lean_IR_EmitC_emitInitFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__3);
l_Lean_IR_EmitC_emitInitFn___closed__4 = _init_l_Lean_IR_EmitC_emitInitFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__4);
l_Lean_IR_EmitC_emitInitFn___closed__5 = _init_l_Lean_IR_EmitC_emitInitFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__5);
l_Lean_IR_EmitC_emitInitFn___closed__6 = _init_l_Lean_IR_EmitC_emitInitFn___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__6);
l_Lean_IR_EmitC_emitInitFn___closed__7 = _init_l_Lean_IR_EmitC_emitInitFn___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__7);
l_Lean_IR_EmitC_emitInitFn___closed__8 = _init_l_Lean_IR_EmitC_emitInitFn___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__8);
l_Lean_IR_EmitC_emitInitFn___closed__9 = _init_l_Lean_IR_EmitC_emitInitFn___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__9);
l_Lean_IR_EmitC_emitInitFn___closed__10 = _init_l_Lean_IR_EmitC_emitInitFn___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__10);
l_Lean_IR_EmitC_main___closed__0 = _init_l_Lean_IR_EmitC_main___closed__0();
lean_mark_persistent(l_Lean_IR_EmitC_main___closed__0);
l_Lean_IR_EmitC_main___closed__1 = _init_l_Lean_IR_EmitC_main___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_main___closed__1);
l_Lean_IR_emitC___closed__0 = _init_l_Lean_IR_emitC___closed__0();
lean_mark_persistent(l_Lean_IR_emitC___closed__0);
l_Lean_IR_emitC___closed__1 = _init_l_Lean_IR_emitC___closed__1();
lean_mark_persistent(l_Lean_IR_emitC___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
