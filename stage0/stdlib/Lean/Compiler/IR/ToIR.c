// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM Lean.Compiler.IR.ToIRType Lean.CoreM Lean.Environment
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
static lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__5;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3;
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__11;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
lean_object* l_Lean_IR_CtorInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__16;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__5;
static lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__3;
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__15;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__1;
extern lean_object* l_Lean_IR_declMapExt;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__3;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity_spec__0(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__14;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__6;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__7;
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__1;
extern lean_object* l_Lean_IR_instInhabitedArg;
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__8;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object**);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_getCtorLayout(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_IR_nameToIRType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__1;
static lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__2;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__9;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIR___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2;
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_IR_ToIR_M_run___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_M_run___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ToIR_M_run___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_M_run___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_IR_ToIR_M_run___redArg___closed__4;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_IR_ToIR_M_run___redArg___closed__5;
x_6 = lean_st_mk_ref(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = lean_apply_4(x_1, x_7, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(142u);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__1;
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__3;
x_5 = lean_panic_fn(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_2);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = l_Lean_IR_instInhabitedArg;
x_11 = lean_array_get_size(x_9);
x_12 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_9, x_23);
lean_dec_ref(x_9);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_10, x_1, x_24);
lean_dec(x_24);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_6);
x_28 = l_Lean_IR_instInhabitedArg;
x_29 = lean_array_get_size(x_27);
x_30 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_27, x_41);
lean_dec_ref(x_27);
x_43 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_28, x_1, x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_26);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getFVarValue(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_9, x_23);
lean_dec_ref(x_9);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_10, x_1, x_24);
lean_dec(x_24);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_6);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get_size(x_27);
x_30 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_27, x_41);
lean_dec_ref(x_27);
x_43 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_28, x_1, x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_26);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getJoinPointValue(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_10 = x_5;
} else {
 lean_dec_ref(x_5);
 x_10 = lean_box(0);
}
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_25 = 32;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = 16;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_usize_land(x_31, x_34);
x_36 = lean_array_uget(x_22, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_1, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc_ref(x_22);
lean_inc(x_21);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_39 = lean_ctor_get(x_7, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_7, 0);
lean_dec(x_40);
lean_inc(x_9);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_9);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_21, x_42);
lean_dec(x_21);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_36);
x_45 = lean_array_uset(x_22, x_35, x_44);
x_46 = lean_unsigned_to_nat(4u);
x_47 = lean_nat_mul(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_45);
lean_ctor_set(x_7, 1, x_52);
lean_ctor_set(x_7, 0, x_43);
x_11 = x_7;
goto block_20;
}
else
{
lean_ctor_set(x_7, 1, x_45);
lean_ctor_set(x_7, 0, x_43);
x_11 = x_7;
goto block_20;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_7);
lean_inc(x_9);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_9);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_21, x_54);
lean_dec(x_21);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_36);
x_57 = lean_array_uset(x_22, x_35, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
x_11 = x_65;
goto block_20;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
x_11 = x_66;
goto block_20;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_1);
x_11 = x_7;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_9, x_12);
if (lean_is_scalar(x_10)) {
 x_14 = lean_alloc_ctor(0, 3, 0);
} else {
 x_14 = x_10;
}
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_st_ref_set(x_2, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_11 = x_6;
} else {
 lean_dec_ref(x_6);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_box(0);
x_23 = lean_array_get_size(x_13);
x_24 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_25 = 32;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = 16;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_usize_land(x_31, x_34);
x_36 = lean_array_uget(x_13, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_1, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc_ref(x_13);
lean_inc(x_12);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_39 = lean_ctor_get(x_7, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_7, 0);
lean_dec(x_40);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_2);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_12, x_42);
lean_dec(x_12);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_36);
x_45 = lean_array_uset(x_13, x_35, x_44);
x_46 = lean_unsigned_to_nat(4u);
x_47 = lean_nat_mul(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_45);
lean_ctor_set(x_7, 1, x_52);
lean_ctor_set(x_7, 0, x_43);
x_15 = x_7;
goto block_22;
}
else
{
lean_ctor_set(x_7, 1, x_45);
lean_ctor_set(x_7, 0, x_43);
x_15 = x_7;
goto block_22;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_7);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_2);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_12, x_54);
lean_dec(x_12);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_36);
x_57 = lean_array_uset(x_13, x_35, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
x_15 = x_65;
goto block_22;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
x_15 = x_66;
goto block_22;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_15 = x_7;
goto block_22;
}
block_22:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
if (lean_is_scalar(x_11)) {
 x_16 = lean_alloc_ctor(0, 3, 0);
} else {
 x_16 = x_11;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_10);
x_17 = lean_st_ref_set(x_3, x_16, x_8);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_ctor_set(x_4, 2, x_9);
x_10 = lean_st_ref_set(x_1, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_st_ref_set(x_1, x_20, x_5);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_newVar___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_10 = x_5;
} else {
 lean_dec_ref(x_5);
 x_10 = lean_box(0);
}
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_25 = 32;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = 16;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_usize_land(x_31, x_34);
x_36 = lean_array_uget(x_22, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_1, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc_ref(x_22);
lean_inc(x_21);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_39 = lean_ctor_get(x_8, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_21, x_41);
lean_dec(x_21);
lean_inc(x_9);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_36);
x_44 = lean_array_uset(x_22, x_35, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_44);
lean_ctor_set(x_8, 1, x_51);
lean_ctor_set(x_8, 0, x_42);
x_11 = x_8;
goto block_20;
}
else
{
lean_ctor_set(x_8, 1, x_44);
lean_ctor_set(x_8, 0, x_42);
x_11 = x_8;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_8);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_21, x_52);
lean_dec(x_21);
lean_inc(x_9);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_9);
lean_ctor_set(x_54, 2, x_36);
x_55 = lean_array_uset(x_22, x_35, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
x_11 = x_63;
goto block_20;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_55);
x_11 = x_64;
goto block_20;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_1);
x_11 = x_8;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_9, x_12);
if (lean_is_scalar(x_10)) {
 x_14 = lean_alloc_ctor(0, 3, 0);
} else {
 x_14 = x_10;
}
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_st_ref_set(x_2, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_10 = x_5;
} else {
 lean_dec_ref(x_5);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_box(0);
x_22 = lean_array_get_size(x_12);
x_23 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1560_(x_1);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_12, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_inc_ref(x_12);
lean_inc(x_11);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_38 = lean_ctor_get(x_6, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_6, 0);
lean_dec(x_39);
x_40 = lean_box(1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_11, x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_35);
x_44 = lean_array_uset(x_12, x_34, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_44);
lean_ctor_set(x_6, 1, x_51);
lean_ctor_set(x_6, 0, x_42);
x_14 = x_6;
goto block_21;
}
else
{
lean_ctor_set(x_6, 1, x_44);
lean_ctor_set(x_6, 0, x_42);
x_14 = x_6;
goto block_21;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_6);
x_52 = lean_box(1);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_11, x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_35);
x_56 = lean_array_uset(x_12, x_34, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ToIR_bindVar_spec__1___redArg(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_63);
x_14 = x_64;
goto block_21;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_56);
x_14 = x_65;
goto block_21;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_1);
x_14 = x_6;
goto block_21;
}
block_21:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
if (lean_is_scalar(x_10)) {
 x_15 = lean_alloc_ctor(0, 3, 0);
} else {
 x_15 = x_10;
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_9);
x_16 = lean_st_ref_set(x_2, x_15, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_ir_find_env_decl(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_ir_find_env_decl(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declMapExt;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___redArg___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = l_Lean_IR_ToIR_addDecl___redArg___closed__0;
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_box(0);
x_14 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_10, x_8, x_1, x_12, x_13);
lean_dec(x_12);
x_15 = l_Lean_IR_ToIR_addDecl___redArg___closed__3;
lean_ctor_set(x_5, 5, x_15);
lean_ctor_set(x_5, 0, x_14);
x_16 = lean_st_ref_set(x_2, x_5, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 3);
x_27 = lean_ctor_get(x_5, 4);
x_28 = lean_ctor_get(x_5, 6);
x_29 = lean_ctor_get(x_5, 7);
x_30 = lean_ctor_get(x_5, 8);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_31 = l_Lean_IR_ToIR_addDecl___redArg___closed__0;
x_32 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_box(0);
x_35 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_31, x_23, x_1, x_33, x_34);
lean_dec(x_33);
x_36 = l_Lean_IR_ToIR_addDecl___redArg___closed__3;
x_37 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set(x_37, 3, x_26);
lean_ctor_set(x_37, 4, x_27);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set(x_37, 6, x_28);
lean_ctor_set(x_37, 7, x_29);
lean_ctor_set(x_37, 8, x_30);
x_38 = lean_st_ref_set(x_2, x_37, x_6);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_3 = x_1;
} else {
 lean_dec_ref(x_1);
 x_3 = lean_box(0);
}
x_8 = lean_cstr_to_nat("4294967296");
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(8);
x_4 = x_10;
goto block_7;
}
else
{
lean_object* x_11; 
x_11 = lean_box(12);
x_4 = x_11;
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
if (lean_is_scalar(x_3)) {
 x_5 = lean_alloc_ctor(0, 1, 0);
} else {
 x_5 = x_3;
}
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
case 2:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_20 = lean_uint8_to_nat(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
case 3:
{
uint16_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get_uint16(x_1, 0);
lean_dec_ref(x_1);
x_25 = lean_uint16_to_nat(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
case 4:
{
uint32_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_30 = lean_uint32_to_nat(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
case 5:
{
uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_35 = lean_uint64_to_nat(x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_box(4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
default: 
{
uint64_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_40 = lean_uint64_to_nat(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_box(5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_ToIR_getFVarValue___redArg(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerArg___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1;
x_2 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerProj___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(6);
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_Lean_IR_ToIR_lowerProj___closed__0;
return x_4;
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 1, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
case 2:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_16);
x_17 = lean_box(5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
default: 
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_ctor_get(x_3, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_nat_add(x_27, x_28);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 0, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_ctor_get(x_3, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_2, 3);
x_36 = lean_nat_add(x_34, x_35);
x_37 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_1);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerProj(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
x_9 = l_Lean_IR_ToIR_bindVar___redArg(x_6, x_2, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_IR_toIRType(x_7, x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_8);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerParam(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0;
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1;
x_18 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2;
lean_inc_ref(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = l_Lean_IR_instInhabitedFnBody;
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_4(x_28, x_2, x_3, x_4, x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_34 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1;
x_35 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2;
lean_inc_ref(x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_30);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_41, 0, x_31);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_7);
x_44 = l_Lean_IR_instInhabitedFnBody;
x_45 = l_instInhabitedOfMonad___redArg(x_43, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_4(x_46, x_2, x_3, x_4, x_5);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1;
x_55 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2;
lean_inc_ref(x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_50);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
x_64 = l_ReaderT_instMonad___redArg(x_63);
x_65 = l_Lean_IR_instInhabitedFnBody;
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_1);
x_68 = lean_apply_4(x_67, x_2, x_3, x_4, x_5);
return x_68;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerAlt.loop", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mismatched fields and params", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2;
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(282u);
x_4 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_48; lean_object* x_55; uint8_t x_56; 
x_55 = lean_array_get_size(x_4);
x_56 = lean_nat_dec_lt(x_6, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_48 = x_57;
goto block_54;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_array_fget_borrowed(x_4, x_6);
lean_inc_ref(x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_48 = x_59;
goto block_54;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3;
x_16 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_15, x_11, x_12, x_13, x_14);
return x_16;
}
block_47:
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_IR_ToIR_lowerCode(x_2, x_7, x_8, x_9, x_10);
return x_20;
}
else
{
lean_dec_ref(x_19);
lean_dec_ref(x_2);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
goto block_17;
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_18);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
lean_inc(x_1);
x_23 = l_Lean_IR_ToIR_lowerProj(x_1, x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_IR_ToIR_bindVar___redArg(x_27, x_7, x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_6, x_31);
lean_dec(x_6);
x_33 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_32, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_39, 2, x_26);
lean_ctor_set(x_39, 3, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_dec(x_29);
lean_dec_ref(x_26);
lean_dec(x_25);
return x_33;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_23);
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
x_42 = l_Lean_IR_ToIR_bindErased___redArg(x_41, x_7, x_10);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_6, x_44);
lean_dec(x_6);
x_6 = x_45;
x_10 = x_43;
goto _start;
}
}
}
}
block_54:
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_array_get_size(x_5);
x_50 = lean_nat_dec_lt(x_6, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_18 = x_48;
x_19 = x_51;
goto block_47;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_array_fget_borrowed(x_5, x_6);
lean_inc(x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_18 = x_48;
x_19 = x_53;
goto block_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_3, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
x_11 = l_Lean_IR_ToIR_lowerParam(x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_12);
x_2 = x_17;
x_3 = x_18;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_IR_ToIR_lowerArg___redArg(x_8, x_4, x_5);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_15;
x_3 = x_16;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_4, x_3);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_IR_ToIR_lowerAlt(x_1, x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_16, x_3, x_13);
x_3 = x_18;
x_4 = x_19;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_IR_ToIR_bindErased___redArg(x_9, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all local functions should be λ-lifted", 39, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(137u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("erased inductive should only have one case", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__3;
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_unsigned_to_nat(127u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_ToIR_lowerLet(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_1);
x_9 = l_Lean_IR_ToIR_lowerCode___closed__2;
x_10 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_11, 4);
lean_inc_ref(x_15);
lean_dec_ref(x_11);
x_16 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_13, x_2, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_array_size(x_14);
x_20 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
x_21 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_19, x_20, x_14, x_2, x_3, x_4, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_24 = l_Lean_IR_ToIR_lowerCode(x_15, x_2, x_3, x_4, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lean_IR_ToIR_lowerCode(x_12, x_2, x_3, x_4, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_17);
return x_27;
}
}
else
{
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_24;
}
}
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 3:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_40);
lean_dec_ref(x_1);
x_41 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_39, x_2, x_5);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_array_size(x_40);
x_45 = 0;
x_46 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_44, x_45, x_40, x_2, x_43);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set_tag(x_41, 11);
lean_ctor_set(x_41, 1, x_48);
lean_ctor_set(x_46, 0, x_41);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set_tag(x_41, 11);
lean_ctor_set(x_41, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_array_size(x_40);
x_55 = 0;
x_56 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_54, x_55, x_40, x_2, x_53);
lean_dec(x_2);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_57);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
case 4:
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_62);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 2);
x_66 = lean_ctor_get(x_62, 3);
x_67 = lean_ctor_get(x_62, 1);
lean_dec(x_67);
x_68 = l_Lean_IR_ToIR_getFVarValue___redArg(x_65, x_2, x_5);
lean_dec(x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec_ref(x_69);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_64);
x_72 = l_Lean_IR_nameToIRType(x_64, x_3, x_4, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_array_size(x_66);
x_76 = 0;
lean_inc(x_71);
x_77 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_71, x_75, x_76, x_66, x_2, x_3, x_4, x_74);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_ctor_set_tag(x_62, 9);
lean_ctor_set(x_62, 3, x_79);
lean_ctor_set(x_62, 2, x_73);
lean_ctor_set(x_62, 1, x_71);
lean_ctor_set(x_77, 0, x_62);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 0);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_77);
lean_ctor_set_tag(x_62, 9);
lean_ctor_set(x_62, 3, x_80);
lean_ctor_set(x_62, 2, x_73);
lean_ctor_set(x_62, 1, x_71);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_62);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_73);
lean_dec(x_71);
lean_free_object(x_62);
lean_dec(x_64);
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_77);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_71);
lean_free_object(x_62);
lean_dec_ref(x_66);
lean_dec(x_64);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_72);
if (x_87 == 0)
{
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_72);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_free_object(x_62);
lean_dec(x_64);
x_91 = lean_ctor_get(x_68, 1);
lean_inc(x_91);
lean_dec_ref(x_68);
x_92 = lean_array_get_size(x_66);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_dec_eq(x_92, x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_66);
x_95 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_96 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_95, x_2, x_3, x_4, x_91);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_array_fget(x_66, x_97);
lean_dec_ref(x_66);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_98, 2);
lean_inc_ref(x_100);
lean_dec_ref(x_98);
x_101 = lean_array_get_size(x_99);
x_102 = lean_nat_dec_lt(x_97, x_101);
if (x_102 == 0)
{
lean_dec(x_101);
lean_dec_ref(x_99);
x_1 = x_100;
x_5 = x_91;
goto _start;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_101, x_101);
if (x_104 == 0)
{
lean_dec(x_101);
lean_dec_ref(x_99);
x_1 = x_100;
x_5 = x_91;
goto _start;
}
else
{
lean_object* x_106; size_t x_107; size_t x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_box(0);
x_107 = 0;
x_108 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_109 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_99, x_107, x_108, x_106, x_2, x_91);
lean_dec_ref(x_99);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec_ref(x_109);
x_1 = x_100;
x_5 = x_110;
goto _start;
}
}
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_98, 0);
lean_inc_ref(x_112);
lean_dec_ref(x_98);
x_1 = x_112;
x_5 = x_91;
goto _start;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_62, 0);
x_115 = lean_ctor_get(x_62, 2);
x_116 = lean_ctor_get(x_62, 3);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_62);
x_117 = l_Lean_IR_ToIR_getFVarValue___redArg(x_115, x_2, x_5);
lean_dec(x_115);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec_ref(x_118);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_114);
x_121 = l_Lean_IR_nameToIRType(x_114, x_3, x_4, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; size_t x_124; size_t x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = lean_array_size(x_116);
x_125 = 0;
lean_inc(x_120);
x_126 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_120, x_124, x_125, x_116, x_2, x_3, x_4, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_130, 0, x_114);
lean_ctor_set(x_130, 1, x_120);
lean_ctor_set(x_130, 2, x_122);
lean_ctor_set(x_130, 3, x_127);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_114);
x_132 = lean_ctor_get(x_126, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_134 = x_126;
} else {
 lean_dec_ref(x_126);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_120);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_136 = lean_ctor_get(x_121, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_121, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_138 = x_121;
} else {
 lean_dec_ref(x_121);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_114);
x_140 = lean_ctor_get(x_117, 1);
lean_inc(x_140);
lean_dec_ref(x_117);
x_141 = lean_array_get_size(x_116);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_dec_eq(x_141, x_142);
lean_dec(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_116);
x_144 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_145 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_144, x_2, x_3, x_4, x_140);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_array_fget(x_116, x_146);
lean_dec_ref(x_116);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_147, 2);
lean_inc_ref(x_149);
lean_dec_ref(x_147);
x_150 = lean_array_get_size(x_148);
x_151 = lean_nat_dec_lt(x_146, x_150);
if (x_151 == 0)
{
lean_dec(x_150);
lean_dec_ref(x_148);
x_1 = x_149;
x_5 = x_140;
goto _start;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_150, x_150);
if (x_153 == 0)
{
lean_dec(x_150);
lean_dec_ref(x_148);
x_1 = x_149;
x_5 = x_140;
goto _start;
}
else
{
lean_object* x_155; size_t x_156; size_t x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_box(0);
x_156 = 0;
x_157 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_158 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_148, x_156, x_157, x_155, x_2, x_140);
lean_dec_ref(x_148);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec_ref(x_158);
x_1 = x_149;
x_5 = x_159;
goto _start;
}
}
}
else
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_161);
lean_dec_ref(x_147);
x_1 = x_161;
x_5 = x_140;
goto _start;
}
}
}
}
}
case 5:
{
uint8_t x_163; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_163 = !lean_is_exclusive(x_1);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_1, 0);
x_165 = l_Lean_IR_ToIR_getFVarValue___redArg(x_164, x_2, x_5);
lean_dec(x_2);
lean_dec(x_164);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_165, 0);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_167);
lean_ctor_set(x_165, 0, x_1);
return x_165;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_165, 0);
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_165);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_1);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_1, 0);
lean_inc(x_171);
lean_dec(x_1);
x_172 = l_Lean_IR_ToIR_getFVarValue___redArg(x_171, x_2, x_5);
lean_dec(x_2);
lean_dec(x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_176, 0, x_173);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_174);
return x_177;
}
}
default: 
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_178 = lean_box(12);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_5);
return x_179;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
lean_inc(x_5);
lean_inc_ref(x_4);
x_10 = l_Lean_IR_getCtorLayout(x_7, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_14, x_8, x_15, x_16, x_3, x_4, x_5, x_12);
lean_dec_ref(x_15);
lean_dec_ref(x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_17, 0, x_11);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_11, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_11);
lean_dec_ref(x_14);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_27, x_8, x_28, x_29, x_3, x_4, x_5, x_12);
lean_dec_ref(x_28);
lean_dec_ref(x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_27);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = l_Lean_IR_ToIR_lowerCode(x_45, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set(x_2, 0, x_48);
lean_ctor_set(x_46, 0, x_2);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_2, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_free_object(x_2);
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
lean_dec(x_2);
x_57 = l_Lean_IR_ToIR_lowerCode(x_56, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 2);
x_10 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
x_11 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
x_19 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
lean_inc(x_17);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_17);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_MessageData_tagWithErrorName(x_2, x_1);
x_8 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(x_7, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_16; 
x_16 = lean_array_fget_borrowed(x_1, x_6);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_2);
x_17 = lean_array_get_borrowed(x_2, x_3, x_6);
lean_inc(x_17);
x_18 = lean_array_push(x_5, x_17);
x_8 = x_18;
x_9 = x_7;
goto block_15;
}
else
{
x_8 = x_5;
x_9 = x_7;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_12 = lean_nat_dec_lt(x_11, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
x_5 = x_8;
x_6 = x_11;
x_7 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_1, x_2, x_3, x_8, x_10, x_11, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("projection of non-structure type", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_unsigned_to_nat(149u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reference to unbound name", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(210u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dependsOnNoncomputable", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 0:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 3);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_IR_ToIR_bindVar___redArg(x_16, x_3, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lean_IR_ToIR_lowerLitValue(x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set_tag(x_14, 11);
lean_ctor_set(x_14, 0, x_26);
lean_ctor_set(x_1, 3, x_30);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_23);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set_tag(x_14, 11);
lean_ctor_set(x_14, 0, x_26);
lean_ctor_set(x_1, 3, x_31);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
lean_free_object(x_14);
lean_free_object(x_1);
return x_28;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = l_Lean_IR_ToIR_bindVar___redArg(x_16, x_3, x_6);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = l_Lean_IR_ToIR_lowerLitValue(x_34);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_1, 3, x_42);
lean_ctor_set(x_1, 2, x_45);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_36);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_36);
lean_free_object(x_1);
return x_41;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_48);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_49 = x_14;
} else {
 lean_dec_ref(x_14);
 x_49 = lean_box(0);
}
x_50 = l_Lean_IR_ToIR_bindVar___redArg(x_47, x_3, x_6);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Lean_IR_ToIR_lowerLitValue(x_48);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_60 = lean_alloc_ctor(11, 1, 0);
} else {
 x_60 = x_49;
 lean_ctor_set_tag(x_60, 11);
}
lean_ctor_set(x_60, 0, x_54);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set(x_61, 1, x_55);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_57);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
else
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_49);
return x_56;
}
}
}
case 1:
{
lean_object* x_63; 
x_63 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_63;
}
case 2:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_1);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_1, 0);
x_66 = lean_ctor_get(x_1, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_1, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_14, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_14, 2);
lean_inc(x_71);
lean_dec_ref(x_14);
x_72 = l_Lean_IR_ToIR_getFVarValue___redArg(x_71, x_3, x_6);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_st_ref_get(x_5, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_79);
lean_dec(x_77);
x_80 = 0;
x_81 = l_Lean_Environment_find_x3f(x_79, x_69, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_dec(x_75);
lean_dec(x_70);
lean_free_object(x_1);
lean_dec(x_65);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_78;
goto block_13;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
if (lean_obj_tag(x_82) == 5)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_83);
lean_dec_ref(x_82);
x_84 = lean_ctor_get(x_83, 4);
lean_inc(x_84);
lean_dec_ref(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_dec(x_75);
lean_dec(x_70);
lean_free_object(x_1);
lean_dec(x_65);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_78;
goto block_13;
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 1);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec_ref(x_84);
lean_inc(x_5);
lean_inc_ref(x_4);
x_87 = l_Lean_IR_getCtorLayout(x_86, x_4, x_5, x_78);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_91);
lean_dec(x_88);
x_92 = lean_box(0);
x_93 = lean_array_get(x_92, x_91, x_70);
lean_dec(x_70);
lean_dec_ref(x_91);
x_94 = l_Lean_IR_ToIR_lowerProj(x_75, x_90, x_93);
lean_dec_ref(x_90);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc_ref(x_97);
lean_dec_ref(x_95);
x_98 = l_Lean_IR_ToIR_bindVar___redArg(x_65, x_3, x_89);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_101, 0);
lean_ctor_set(x_1, 3, x_103);
lean_ctor_set(x_1, 2, x_97);
lean_ctor_set(x_1, 1, x_96);
lean_ctor_set(x_1, 0, x_99);
lean_ctor_set(x_101, 0, x_1);
return x_101;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_101, 0);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_101);
lean_ctor_set(x_1, 3, x_104);
lean_ctor_set(x_1, 2, x_97);
lean_ctor_set(x_1, 1, x_96);
lean_ctor_set(x_1, 0, x_99);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_1);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
lean_dec(x_99);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_free_object(x_1);
return x_101;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_94);
lean_free_object(x_1);
x_107 = l_Lean_IR_ToIR_bindErased___redArg(x_65, x_3, x_89);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_108);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_75);
lean_dec(x_70);
lean_free_object(x_1);
lean_dec(x_65);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_110 = !lean_is_exclusive(x_87);
if (x_110 == 0)
{
return x_87;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_87, 0);
x_112 = lean_ctor_get(x_87, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_87);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_dec_ref(x_84);
lean_dec(x_75);
lean_dec(x_70);
lean_free_object(x_1);
lean_dec(x_65);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_78;
goto block_13;
}
}
}
else
{
lean_dec(x_82);
lean_dec(x_75);
lean_dec(x_70);
lean_free_object(x_1);
lean_dec(x_65);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_78;
goto block_13;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_70);
lean_dec(x_69);
lean_free_object(x_1);
x_114 = lean_ctor_get(x_72, 1);
lean_inc(x_114);
lean_dec_ref(x_72);
x_115 = l_Lean_IR_ToIR_bindErased___redArg(x_65, x_3, x_114);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
lean_dec(x_1);
x_119 = lean_ctor_get(x_14, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_14, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_14, 2);
lean_inc(x_121);
lean_dec_ref(x_14);
x_122 = l_Lean_IR_ToIR_getFVarValue___redArg(x_121, x_3, x_6);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; 
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
lean_dec_ref(x_123);
x_126 = lean_st_ref_get(x_5, x_124);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_129);
lean_dec(x_127);
x_130 = 0;
x_131 = l_Lean_Environment_find_x3f(x_129, x_119, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_118);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_128;
goto block_13;
}
else
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
if (lean_obj_tag(x_132) == 5)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc_ref(x_133);
lean_dec_ref(x_132);
x_134 = lean_ctor_get(x_133, 4);
lean_inc(x_134);
lean_dec_ref(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_118);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_128;
goto block_13;
}
else
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 1);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec_ref(x_134);
lean_inc(x_5);
lean_inc_ref(x_4);
x_137 = l_Lean_IR_getCtorLayout(x_136, x_4, x_5, x_128);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec_ref(x_137);
x_140 = lean_ctor_get(x_138, 0);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_138, 1);
lean_inc_ref(x_141);
lean_dec(x_138);
x_142 = lean_box(0);
x_143 = lean_array_get(x_142, x_141, x_120);
lean_dec(x_120);
lean_dec_ref(x_141);
x_144 = l_Lean_IR_ToIR_lowerProj(x_125, x_140, x_143);
lean_dec_ref(x_140);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc_ref(x_147);
lean_dec_ref(x_145);
x_148 = l_Lean_IR_ToIR_bindVar___redArg(x_118, x_3, x_139);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec_ref(x_148);
x_151 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
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
x_155 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set(x_155, 1, x_146);
lean_ctor_set(x_155, 2, x_147);
lean_ctor_set(x_155, 3, x_152);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
else
{
lean_dec(x_149);
lean_dec_ref(x_147);
lean_dec(x_146);
return x_151;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec_ref(x_144);
x_157 = l_Lean_IR_ToIR_bindErased___redArg(x_118, x_3, x_139);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_158);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_160 = lean_ctor_get(x_137, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_137, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_162 = x_137;
} else {
 lean_dec_ref(x_137);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_dec_ref(x_134);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_118);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_128;
goto block_13;
}
}
}
else
{
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_118);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_128;
goto block_13;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_120);
lean_dec(x_119);
x_164 = lean_ctor_get(x_122, 1);
lean_inc(x_164);
lean_dec_ref(x_122);
x_165 = l_Lean_IR_ToIR_bindErased___redArg(x_118, x_3, x_164);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_166);
return x_167;
}
}
}
case 3:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; lean_object* x_173; uint8_t x_174; 
x_168 = lean_ctor_get(x_1, 0);
x_169 = lean_ctor_get(x_14, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_170);
lean_dec_ref(x_14);
x_171 = lean_array_size(x_170);
x_172 = 0;
x_173 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_171, x_172, x_170, x_3, x_6);
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_175);
lean_inc(x_169);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_177 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_169, x_175, x_3, x_4, x_5, x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec_ref(x_177);
x_180 = lean_st_ref_get(x_5, x_179);
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_ctor_get(x_180, 1);
x_184 = lean_ctor_get(x_182, 0);
lean_inc_ref(x_184);
lean_dec(x_182);
x_185 = 0;
lean_inc(x_169);
lean_inc_ref(x_184);
x_186 = l_Lean_Environment_find_x3f(x_184, x_169, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec_ref(x_184);
lean_free_object(x_180);
lean_free_object(x_173);
lean_dec(x_175);
lean_dec(x_169);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_187 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_188 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_187, x_3, x_4, x_5, x_183);
return x_188;
}
else
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_186, 0);
switch (lean_obj_tag(x_190)) {
case 0:
{
uint8_t x_191; 
lean_free_object(x_186);
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_192 = lean_ctor_get(x_190, 0);
lean_dec(x_192);
x_193 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_194 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_195 = 1;
x_196 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_195);
lean_ctor_set_tag(x_190, 3);
lean_ctor_set(x_190, 0, x_196);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_190);
lean_ctor_set(x_180, 0, x_194);
x_197 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_197);
lean_ctor_set(x_173, 0, x_180);
x_198 = l_Lean_MessageData_ofFormat(x_173);
x_199 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_193, x_198, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_190);
x_200 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_201 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_202 = 1;
x_203 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_202);
x_204 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_204);
lean_ctor_set(x_180, 0, x_201);
x_205 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_205);
lean_ctor_set(x_173, 0, x_180);
x_206 = l_Lean_MessageData_ofFormat(x_173);
x_207 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_200, x_206, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_207;
}
}
case 2:
{
uint8_t x_208; 
lean_free_object(x_186);
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_208 = !lean_is_exclusive(x_190);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_209 = lean_ctor_get(x_190, 0);
lean_dec(x_209);
x_210 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_211 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_212 = 1;
x_213 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_212);
lean_ctor_set_tag(x_190, 3);
lean_ctor_set(x_190, 0, x_213);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_190);
lean_ctor_set(x_180, 0, x_211);
x_214 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_214);
lean_ctor_set(x_173, 0, x_180);
x_215 = l_Lean_MessageData_ofFormat(x_173);
x_216 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_210, x_215, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_190);
x_217 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_218 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_219 = 1;
x_220 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_219);
x_221 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_221);
lean_ctor_set(x_180, 0, x_218);
x_222 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_222);
lean_ctor_set(x_173, 0, x_180);
x_223 = l_Lean_MessageData_ofFormat(x_173);
x_224 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_217, x_223, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_224;
}
}
case 4:
{
uint8_t x_225; 
lean_free_object(x_186);
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_225 = !lean_is_exclusive(x_190);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_226 = lean_ctor_get(x_190, 0);
lean_dec(x_226);
x_227 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_228 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_229 = 1;
x_230 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_229);
lean_ctor_set_tag(x_190, 3);
lean_ctor_set(x_190, 0, x_230);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_190);
lean_ctor_set(x_180, 0, x_228);
x_231 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_231);
lean_ctor_set(x_173, 0, x_180);
x_232 = l_Lean_MessageData_ofFormat(x_173);
x_233 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_227, x_232, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_190);
x_234 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_235 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_236 = 1;
x_237 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_236);
x_238 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_238);
lean_ctor_set(x_180, 0, x_235);
x_239 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_239);
lean_ctor_set(x_173, 0, x_180);
x_240 = l_Lean_MessageData_ofFormat(x_173);
x_241 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_234, x_240, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_241;
}
}
case 5:
{
uint8_t x_242; 
lean_free_object(x_186);
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_242 = !lean_is_exclusive(x_190);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_190, 0);
lean_dec(x_243);
x_244 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_245 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_246 = 1;
x_247 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_246);
lean_ctor_set_tag(x_190, 3);
lean_ctor_set(x_190, 0, x_247);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_190);
lean_ctor_set(x_180, 0, x_245);
x_248 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_248);
lean_ctor_set(x_173, 0, x_180);
x_249 = l_Lean_MessageData_ofFormat(x_173);
x_250 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_244, x_249, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_190);
x_251 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_252 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_253 = 1;
x_254 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_253);
x_255 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_255);
lean_ctor_set(x_180, 0, x_252);
x_256 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_256);
lean_ctor_set(x_173, 0, x_180);
x_257 = l_Lean_MessageData_ofFormat(x_173);
x_258 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_251, x_257, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_258;
}
}
case 6:
{
uint8_t x_259; 
lean_free_object(x_180);
lean_free_object(x_173);
x_259 = !lean_is_exclusive(x_190);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_190, 0);
lean_inc(x_169);
x_261 = l_Lean_isExtern(x_184, x_169);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_262 = x_1;
} else {
 lean_dec_ref(x_1);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_260, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_260, 3);
lean_inc(x_265);
lean_dec_ref(x_260);
lean_inc(x_5);
lean_inc_ref(x_4);
x_266 = l_Lean_IR_nameToIRType(x_263, x_4, x_5, x_183);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec_ref(x_266);
x_269 = l_Lean_IR_IRType_isScalar(x_267);
if (x_269 == 0)
{
lean_object* x_270; 
lean_dec(x_267);
lean_dec(x_264);
lean_free_object(x_190);
lean_free_object(x_186);
lean_inc(x_5);
lean_inc_ref(x_4);
x_270 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_268);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_306; uint8_t x_307; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = lean_ctor_get(x_271, 0);
lean_inc_ref(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc_ref(x_274);
lean_dec(x_271);
x_275 = lean_array_get_size(x_274);
x_276 = lean_unsigned_to_nat(0u);
x_277 = lean_array_get_size(x_175);
x_278 = l_Array_extract___redArg(x_175, x_265, x_277);
lean_dec(x_175);
x_306 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_307 = lean_nat_dec_lt(x_276, x_275);
if (x_307 == 0)
{
lean_dec(x_275);
x_279 = x_306;
x_280 = x_272;
goto block_305;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = l_Lean_IR_instInhabitedArg;
x_309 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_274, x_308, x_278, x_275, x_306, x_276, x_272);
lean_dec(x_275);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec_ref(x_309);
x_279 = x_310;
x_280 = x_311;
goto block_305;
}
block_305:
{
lean_object* x_281; uint8_t x_282; 
x_281 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_280);
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_281, 0);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
x_285 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_273, x_274, x_278, x_283, x_3, x_4, x_5, x_284);
lean_dec_ref(x_278);
lean_dec_ref(x_274);
if (lean_obj_tag(x_285) == 0)
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_285, 0);
x_288 = l_Lean_IR_CtorInfo_type(x_273);
lean_ctor_set(x_281, 1, x_279);
lean_ctor_set(x_281, 0, x_273);
if (lean_is_scalar(x_262)) {
 x_289 = lean_alloc_ctor(0, 4, 0);
} else {
 x_289 = x_262;
}
lean_ctor_set(x_289, 0, x_283);
lean_ctor_set(x_289, 1, x_288);
lean_ctor_set(x_289, 2, x_281);
lean_ctor_set(x_289, 3, x_287);
lean_ctor_set(x_285, 0, x_289);
return x_285;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_285, 0);
x_291 = lean_ctor_get(x_285, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_285);
x_292 = l_Lean_IR_CtorInfo_type(x_273);
lean_ctor_set(x_281, 1, x_279);
lean_ctor_set(x_281, 0, x_273);
if (lean_is_scalar(x_262)) {
 x_293 = lean_alloc_ctor(0, 4, 0);
} else {
 x_293 = x_262;
}
lean_ctor_set(x_293, 0, x_283);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_293, 2, x_281);
lean_ctor_set(x_293, 3, x_290);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_291);
return x_294;
}
}
else
{
lean_free_object(x_281);
lean_dec(x_283);
lean_dec_ref(x_279);
lean_dec_ref(x_273);
lean_dec(x_262);
return x_285;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_281, 0);
x_296 = lean_ctor_get(x_281, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_281);
lean_inc(x_295);
x_297 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_273, x_274, x_278, x_295, x_3, x_4, x_5, x_296);
lean_dec_ref(x_278);
lean_dec_ref(x_274);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = l_Lean_IR_CtorInfo_type(x_273);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_273);
lean_ctor_set(x_302, 1, x_279);
if (lean_is_scalar(x_262)) {
 x_303 = lean_alloc_ctor(0, 4, 0);
} else {
 x_303 = x_262;
}
lean_ctor_set(x_303, 0, x_295);
lean_ctor_set(x_303, 1, x_301);
lean_ctor_set(x_303, 2, x_302);
lean_ctor_set(x_303, 3, x_298);
if (lean_is_scalar(x_300)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_300;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_299);
return x_304;
}
else
{
lean_dec(x_295);
lean_dec_ref(x_279);
lean_dec_ref(x_273);
lean_dec(x_262);
return x_297;
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_265);
lean_dec(x_262);
lean_dec(x_175);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_312 = !lean_is_exclusive(x_270);
if (x_312 == 0)
{
return x_270;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_270, 0);
x_314 = lean_ctor_get(x_270, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_270);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_265);
lean_dec(x_175);
lean_dec(x_169);
x_316 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_268);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec_ref(x_316);
x_319 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_318);
if (lean_obj_tag(x_319) == 0)
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_319, 0);
lean_ctor_set_tag(x_190, 0);
lean_ctor_set(x_190, 0, x_264);
lean_ctor_set_tag(x_186, 11);
if (lean_is_scalar(x_262)) {
 x_322 = lean_alloc_ctor(0, 4, 0);
} else {
 x_322 = x_262;
}
lean_ctor_set(x_322, 0, x_317);
lean_ctor_set(x_322, 1, x_267);
lean_ctor_set(x_322, 2, x_186);
lean_ctor_set(x_322, 3, x_321);
lean_ctor_set(x_319, 0, x_322);
return x_319;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_323 = lean_ctor_get(x_319, 0);
x_324 = lean_ctor_get(x_319, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_319);
lean_ctor_set_tag(x_190, 0);
lean_ctor_set(x_190, 0, x_264);
lean_ctor_set_tag(x_186, 11);
if (lean_is_scalar(x_262)) {
 x_325 = lean_alloc_ctor(0, 4, 0);
} else {
 x_325 = x_262;
}
lean_ctor_set(x_325, 0, x_317);
lean_ctor_set(x_325, 1, x_267);
lean_ctor_set(x_325, 2, x_186);
lean_ctor_set(x_325, 3, x_323);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_dec(x_317);
lean_dec(x_267);
lean_dec(x_264);
lean_dec(x_262);
lean_free_object(x_190);
lean_free_object(x_186);
return x_319;
}
}
}
else
{
uint8_t x_327; 
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_262);
lean_free_object(x_190);
lean_free_object(x_186);
lean_dec(x_175);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_327 = !lean_is_exclusive(x_266);
if (x_327 == 0)
{
return x_266;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_266, 0);
x_329 = lean_ctor_get(x_266, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_266);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
else
{
lean_object* x_331; 
lean_free_object(x_190);
lean_dec_ref(x_260);
lean_free_object(x_186);
x_331 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_175, x_3, x_4, x_5, x_183);
return x_331;
}
}
else
{
lean_object* x_332; uint8_t x_333; 
x_332 = lean_ctor_get(x_190, 0);
lean_inc(x_332);
lean_dec(x_190);
lean_inc(x_169);
x_333 = l_Lean_isExtern(x_184, x_169);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_334 = x_1;
} else {
 lean_dec_ref(x_1);
 x_334 = lean_box(0);
}
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_332, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_332, 3);
lean_inc(x_337);
lean_dec_ref(x_332);
lean_inc(x_5);
lean_inc_ref(x_4);
x_338 = l_Lean_IR_nameToIRType(x_335, x_4, x_5, x_183);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec_ref(x_338);
x_341 = l_Lean_IR_IRType_isScalar(x_339);
if (x_341 == 0)
{
lean_object* x_342; 
lean_dec(x_339);
lean_dec(x_336);
lean_free_object(x_186);
lean_inc(x_5);
lean_inc_ref(x_4);
x_342 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_340);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_366; uint8_t x_367; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc_ref(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc_ref(x_346);
lean_dec(x_343);
x_347 = lean_array_get_size(x_346);
x_348 = lean_unsigned_to_nat(0u);
x_349 = lean_array_get_size(x_175);
x_350 = l_Array_extract___redArg(x_175, x_337, x_349);
lean_dec(x_175);
x_366 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_367 = lean_nat_dec_lt(x_348, x_347);
if (x_367 == 0)
{
lean_dec(x_347);
x_351 = x_366;
x_352 = x_344;
goto block_365;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_368 = l_Lean_IR_instInhabitedArg;
x_369 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_346, x_368, x_350, x_347, x_366, x_348, x_344);
lean_dec(x_347);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec_ref(x_369);
x_351 = x_370;
x_352 = x_371;
goto block_365;
}
block_365:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_356 = x_353;
} else {
 lean_dec_ref(x_353);
 x_356 = lean_box(0);
}
lean_inc(x_354);
x_357 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_345, x_346, x_350, x_354, x_3, x_4, x_5, x_355);
lean_dec_ref(x_350);
lean_dec_ref(x_346);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_360 = x_357;
} else {
 lean_dec_ref(x_357);
 x_360 = lean_box(0);
}
x_361 = l_Lean_IR_CtorInfo_type(x_345);
if (lean_is_scalar(x_356)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_356;
}
lean_ctor_set(x_362, 0, x_345);
lean_ctor_set(x_362, 1, x_351);
if (lean_is_scalar(x_334)) {
 x_363 = lean_alloc_ctor(0, 4, 0);
} else {
 x_363 = x_334;
}
lean_ctor_set(x_363, 0, x_354);
lean_ctor_set(x_363, 1, x_361);
lean_ctor_set(x_363, 2, x_362);
lean_ctor_set(x_363, 3, x_358);
if (lean_is_scalar(x_360)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_360;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_359);
return x_364;
}
else
{
lean_dec(x_356);
lean_dec(x_354);
lean_dec_ref(x_351);
lean_dec_ref(x_345);
lean_dec(x_334);
return x_357;
}
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_337);
lean_dec(x_334);
lean_dec(x_175);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_372 = lean_ctor_get(x_342, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_342, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_374 = x_342;
} else {
 lean_dec_ref(x_342);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_337);
lean_dec(x_175);
lean_dec(x_169);
x_376 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_340);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec_ref(x_376);
x_379 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_378);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_382 = x_379;
} else {
 lean_dec_ref(x_379);
 x_382 = lean_box(0);
}
x_383 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_383, 0, x_336);
lean_ctor_set_tag(x_186, 11);
lean_ctor_set(x_186, 0, x_383);
if (lean_is_scalar(x_334)) {
 x_384 = lean_alloc_ctor(0, 4, 0);
} else {
 x_384 = x_334;
}
lean_ctor_set(x_384, 0, x_377);
lean_ctor_set(x_384, 1, x_339);
lean_ctor_set(x_384, 2, x_186);
lean_ctor_set(x_384, 3, x_380);
if (lean_is_scalar(x_382)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_382;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_381);
return x_385;
}
else
{
lean_dec(x_377);
lean_dec(x_339);
lean_dec(x_336);
lean_dec(x_334);
lean_free_object(x_186);
return x_379;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_334);
lean_free_object(x_186);
lean_dec(x_175);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_386 = lean_ctor_get(x_338, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_338, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_388 = x_338;
} else {
 lean_dec_ref(x_338);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
else
{
lean_object* x_390; 
lean_dec_ref(x_332);
lean_free_object(x_186);
x_390 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_175, x_3, x_4, x_5, x_183);
return x_390;
}
}
}
case 7:
{
uint8_t x_391; 
lean_free_object(x_186);
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_391 = !lean_is_exclusive(x_190);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_392 = lean_ctor_get(x_190, 0);
lean_dec(x_392);
x_393 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_394 = 1;
x_395 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_394);
lean_ctor_set_tag(x_190, 3);
lean_ctor_set(x_190, 0, x_395);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_190);
lean_ctor_set(x_180, 0, x_393);
x_396 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_396);
lean_ctor_set(x_173, 0, x_180);
x_397 = l_Lean_MessageData_ofFormat(x_173);
x_398 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_397, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_398;
}
else
{
lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_190);
x_399 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_400 = 1;
x_401 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_400);
x_402 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_402);
lean_ctor_set(x_180, 0, x_399);
x_403 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_403);
lean_ctor_set(x_173, 0, x_180);
x_404 = l_Lean_MessageData_ofFormat(x_173);
x_405 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_404, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_405;
}
}
default: 
{
lean_object* x_406; 
lean_free_object(x_186);
lean_dec(x_190);
lean_dec_ref(x_184);
lean_free_object(x_180);
lean_free_object(x_173);
x_406 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_175, x_3, x_4, x_5, x_183);
return x_406;
}
}
}
else
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_186, 0);
lean_inc(x_407);
lean_dec(x_186);
switch (lean_obj_tag(x_407)) {
case 0:
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_408 = x_407;
} else {
 lean_dec_ref(x_407);
 x_408 = lean_box(0);
}
x_409 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_410 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_411 = 1;
x_412 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_411);
if (lean_is_scalar(x_408)) {
 x_413 = lean_alloc_ctor(3, 1, 0);
} else {
 x_413 = x_408;
 lean_ctor_set_tag(x_413, 3);
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_413);
lean_ctor_set(x_180, 0, x_410);
x_414 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_414);
lean_ctor_set(x_173, 0, x_180);
x_415 = l_Lean_MessageData_ofFormat(x_173);
x_416 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_409, x_415, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_416;
}
case 2:
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_417 = x_407;
} else {
 lean_dec_ref(x_407);
 x_417 = lean_box(0);
}
x_418 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_419 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_420 = 1;
x_421 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_420);
if (lean_is_scalar(x_417)) {
 x_422 = lean_alloc_ctor(3, 1, 0);
} else {
 x_422 = x_417;
 lean_ctor_set_tag(x_422, 3);
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_422);
lean_ctor_set(x_180, 0, x_419);
x_423 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_423);
lean_ctor_set(x_173, 0, x_180);
x_424 = l_Lean_MessageData_ofFormat(x_173);
x_425 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_418, x_424, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_425;
}
case 4:
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_426 = x_407;
} else {
 lean_dec_ref(x_407);
 x_426 = lean_box(0);
}
x_427 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_428 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_429 = 1;
x_430 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_429);
if (lean_is_scalar(x_426)) {
 x_431 = lean_alloc_ctor(3, 1, 0);
} else {
 x_431 = x_426;
 lean_ctor_set_tag(x_431, 3);
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_431);
lean_ctor_set(x_180, 0, x_428);
x_432 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_432);
lean_ctor_set(x_173, 0, x_180);
x_433 = l_Lean_MessageData_ofFormat(x_173);
x_434 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_427, x_433, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_434;
}
case 5:
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_435 = x_407;
} else {
 lean_dec_ref(x_407);
 x_435 = lean_box(0);
}
x_436 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_437 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_438 = 1;
x_439 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_438);
if (lean_is_scalar(x_435)) {
 x_440 = lean_alloc_ctor(3, 1, 0);
} else {
 x_440 = x_435;
 lean_ctor_set_tag(x_440, 3);
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_440);
lean_ctor_set(x_180, 0, x_437);
x_441 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_441);
lean_ctor_set(x_173, 0, x_180);
x_442 = l_Lean_MessageData_ofFormat(x_173);
x_443 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_436, x_442, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_443;
}
case 6:
{
lean_object* x_444; lean_object* x_445; uint8_t x_446; 
lean_free_object(x_180);
lean_free_object(x_173);
x_444 = lean_ctor_get(x_407, 0);
lean_inc_ref(x_444);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_445 = x_407;
} else {
 lean_dec_ref(x_407);
 x_445 = lean_box(0);
}
lean_inc(x_169);
x_446 = l_Lean_isExtern(x_184, x_169);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_447 = x_1;
} else {
 lean_dec_ref(x_1);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_444, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_444, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_444, 3);
lean_inc(x_450);
lean_dec_ref(x_444);
lean_inc(x_5);
lean_inc_ref(x_4);
x_451 = l_Lean_IR_nameToIRType(x_448, x_4, x_5, x_183);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec_ref(x_451);
x_454 = l_Lean_IR_IRType_isScalar(x_452);
if (x_454 == 0)
{
lean_object* x_455; 
lean_dec(x_452);
lean_dec(x_449);
lean_dec(x_445);
lean_inc(x_5);
lean_inc_ref(x_4);
x_455 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_453);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_479; uint8_t x_480; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec_ref(x_455);
x_458 = lean_ctor_get(x_456, 0);
lean_inc_ref(x_458);
x_459 = lean_ctor_get(x_456, 1);
lean_inc_ref(x_459);
lean_dec(x_456);
x_460 = lean_array_get_size(x_459);
x_461 = lean_unsigned_to_nat(0u);
x_462 = lean_array_get_size(x_175);
x_463 = l_Array_extract___redArg(x_175, x_450, x_462);
lean_dec(x_175);
x_479 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_480 = lean_nat_dec_lt(x_461, x_460);
if (x_480 == 0)
{
lean_dec(x_460);
x_464 = x_479;
x_465 = x_457;
goto block_478;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_481 = l_Lean_IR_instInhabitedArg;
x_482 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_459, x_481, x_463, x_460, x_479, x_461, x_457);
lean_dec(x_460);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec_ref(x_482);
x_464 = x_483;
x_465 = x_484;
goto block_478;
}
block_478:
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_465);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_469 = x_466;
} else {
 lean_dec_ref(x_466);
 x_469 = lean_box(0);
}
lean_inc(x_467);
x_470 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_458, x_459, x_463, x_467, x_3, x_4, x_5, x_468);
lean_dec_ref(x_463);
lean_dec_ref(x_459);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
x_474 = l_Lean_IR_CtorInfo_type(x_458);
if (lean_is_scalar(x_469)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_469;
}
lean_ctor_set(x_475, 0, x_458);
lean_ctor_set(x_475, 1, x_464);
if (lean_is_scalar(x_447)) {
 x_476 = lean_alloc_ctor(0, 4, 0);
} else {
 x_476 = x_447;
}
lean_ctor_set(x_476, 0, x_467);
lean_ctor_set(x_476, 1, x_474);
lean_ctor_set(x_476, 2, x_475);
lean_ctor_set(x_476, 3, x_471);
if (lean_is_scalar(x_473)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_473;
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_472);
return x_477;
}
else
{
lean_dec(x_469);
lean_dec(x_467);
lean_dec_ref(x_464);
lean_dec_ref(x_458);
lean_dec(x_447);
return x_470;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_450);
lean_dec(x_447);
lean_dec(x_175);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_485 = lean_ctor_get(x_455, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_455, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_487 = x_455;
} else {
 lean_dec_ref(x_455);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_450);
lean_dec(x_175);
lean_dec(x_169);
x_489 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_453);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
lean_dec_ref(x_489);
x_492 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_491);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_495 = x_492;
} else {
 lean_dec_ref(x_492);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_496 = lean_alloc_ctor(0, 1, 0);
} else {
 x_496 = x_445;
 lean_ctor_set_tag(x_496, 0);
}
lean_ctor_set(x_496, 0, x_449);
x_497 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_497, 0, x_496);
if (lean_is_scalar(x_447)) {
 x_498 = lean_alloc_ctor(0, 4, 0);
} else {
 x_498 = x_447;
}
lean_ctor_set(x_498, 0, x_490);
lean_ctor_set(x_498, 1, x_452);
lean_ctor_set(x_498, 2, x_497);
lean_ctor_set(x_498, 3, x_493);
if (lean_is_scalar(x_495)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_495;
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_494);
return x_499;
}
else
{
lean_dec(x_490);
lean_dec(x_452);
lean_dec(x_449);
lean_dec(x_447);
lean_dec(x_445);
return x_492;
}
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_447);
lean_dec(x_445);
lean_dec(x_175);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_500 = lean_ctor_get(x_451, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_451, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_502 = x_451;
} else {
 lean_dec_ref(x_451);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
else
{
lean_object* x_504; 
lean_dec(x_445);
lean_dec_ref(x_444);
x_504 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_175, x_3, x_4, x_5, x_183);
return x_504;
}
}
case 7:
{
lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec_ref(x_184);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_505 = x_407;
} else {
 lean_dec_ref(x_407);
 x_505 = lean_box(0);
}
x_506 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_507 = 1;
x_508 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_507);
if (lean_is_scalar(x_505)) {
 x_509 = lean_alloc_ctor(3, 1, 0);
} else {
 x_509 = x_505;
 lean_ctor_set_tag(x_509, 3);
}
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set_tag(x_180, 5);
lean_ctor_set(x_180, 1, x_509);
lean_ctor_set(x_180, 0, x_506);
x_510 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_510);
lean_ctor_set(x_173, 0, x_180);
x_511 = l_Lean_MessageData_ofFormat(x_173);
x_512 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_511, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_512;
}
default: 
{
lean_object* x_513; 
lean_dec(x_407);
lean_dec_ref(x_184);
lean_free_object(x_180);
lean_free_object(x_173);
x_513 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_175, x_3, x_4, x_5, x_183);
return x_513;
}
}
}
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; 
x_514 = lean_ctor_get(x_180, 0);
x_515 = lean_ctor_get(x_180, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_180);
x_516 = lean_ctor_get(x_514, 0);
lean_inc_ref(x_516);
lean_dec(x_514);
x_517 = 0;
lean_inc(x_169);
lean_inc_ref(x_516);
x_518 = l_Lean_Environment_find_x3f(x_516, x_169, x_517);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; 
lean_dec_ref(x_516);
lean_free_object(x_173);
lean_dec(x_175);
lean_dec(x_169);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_519 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_520 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_519, x_3, x_4, x_5, x_515);
return x_520;
}
else
{
lean_object* x_521; lean_object* x_522; 
x_521 = lean_ctor_get(x_518, 0);
lean_inc(x_521);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 x_522 = x_518;
} else {
 lean_dec_ref(x_518);
 x_522 = lean_box(0);
}
switch (lean_obj_tag(x_521)) {
case 0:
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_522);
lean_dec_ref(x_516);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_523 = x_521;
} else {
 lean_dec_ref(x_521);
 x_523 = lean_box(0);
}
x_524 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_525 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_526 = 1;
x_527 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_526);
if (lean_is_scalar(x_523)) {
 x_528 = lean_alloc_ctor(3, 1, 0);
} else {
 x_528 = x_523;
 lean_ctor_set_tag(x_528, 3);
}
lean_ctor_set(x_528, 0, x_527);
x_529 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_529, 0, x_525);
lean_ctor_set(x_529, 1, x_528);
x_530 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_530);
lean_ctor_set(x_173, 0, x_529);
x_531 = l_Lean_MessageData_ofFormat(x_173);
x_532 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_524, x_531, x_4, x_5, x_515);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_532;
}
case 2:
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_522);
lean_dec_ref(x_516);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_533 = x_521;
} else {
 lean_dec_ref(x_521);
 x_533 = lean_box(0);
}
x_534 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_535 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_536 = 1;
x_537 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_536);
if (lean_is_scalar(x_533)) {
 x_538 = lean_alloc_ctor(3, 1, 0);
} else {
 x_538 = x_533;
 lean_ctor_set_tag(x_538, 3);
}
lean_ctor_set(x_538, 0, x_537);
x_539 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_539, 0, x_535);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_540);
lean_ctor_set(x_173, 0, x_539);
x_541 = l_Lean_MessageData_ofFormat(x_173);
x_542 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_534, x_541, x_4, x_5, x_515);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_542;
}
case 4:
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_522);
lean_dec_ref(x_516);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_543 = x_521;
} else {
 lean_dec_ref(x_521);
 x_543 = lean_box(0);
}
x_544 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_545 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_546 = 1;
x_547 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_546);
if (lean_is_scalar(x_543)) {
 x_548 = lean_alloc_ctor(3, 1, 0);
} else {
 x_548 = x_543;
 lean_ctor_set_tag(x_548, 3);
}
lean_ctor_set(x_548, 0, x_547);
x_549 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_549, 0, x_545);
lean_ctor_set(x_549, 1, x_548);
x_550 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_550);
lean_ctor_set(x_173, 0, x_549);
x_551 = l_Lean_MessageData_ofFormat(x_173);
x_552 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_544, x_551, x_4, x_5, x_515);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_552;
}
case 5:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_522);
lean_dec_ref(x_516);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_553 = x_521;
} else {
 lean_dec_ref(x_521);
 x_553 = lean_box(0);
}
x_554 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_555 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_556 = 1;
x_557 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_556);
if (lean_is_scalar(x_553)) {
 x_558 = lean_alloc_ctor(3, 1, 0);
} else {
 x_558 = x_553;
 lean_ctor_set_tag(x_558, 3);
}
lean_ctor_set(x_558, 0, x_557);
x_559 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_559, 0, x_555);
lean_ctor_set(x_559, 1, x_558);
x_560 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_560);
lean_ctor_set(x_173, 0, x_559);
x_561 = l_Lean_MessageData_ofFormat(x_173);
x_562 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_554, x_561, x_4, x_5, x_515);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_562;
}
case 6:
{
lean_object* x_563; lean_object* x_564; uint8_t x_565; 
lean_free_object(x_173);
x_563 = lean_ctor_get(x_521, 0);
lean_inc_ref(x_563);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_564 = x_521;
} else {
 lean_dec_ref(x_521);
 x_564 = lean_box(0);
}
lean_inc(x_169);
x_565 = l_Lean_isExtern(x_516, x_169);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_566 = x_1;
} else {
 lean_dec_ref(x_1);
 x_566 = lean_box(0);
}
x_567 = lean_ctor_get(x_563, 1);
lean_inc(x_567);
x_568 = lean_ctor_get(x_563, 2);
lean_inc(x_568);
x_569 = lean_ctor_get(x_563, 3);
lean_inc(x_569);
lean_dec_ref(x_563);
lean_inc(x_5);
lean_inc_ref(x_4);
x_570 = l_Lean_IR_nameToIRType(x_567, x_4, x_5, x_515);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; uint8_t x_573; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec_ref(x_570);
x_573 = l_Lean_IR_IRType_isScalar(x_571);
if (x_573 == 0)
{
lean_object* x_574; 
lean_dec(x_571);
lean_dec(x_568);
lean_dec(x_564);
lean_dec(x_522);
lean_inc(x_5);
lean_inc_ref(x_4);
x_574 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_572);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_598; uint8_t x_599; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec_ref(x_574);
x_577 = lean_ctor_get(x_575, 0);
lean_inc_ref(x_577);
x_578 = lean_ctor_get(x_575, 1);
lean_inc_ref(x_578);
lean_dec(x_575);
x_579 = lean_array_get_size(x_578);
x_580 = lean_unsigned_to_nat(0u);
x_581 = lean_array_get_size(x_175);
x_582 = l_Array_extract___redArg(x_175, x_569, x_581);
lean_dec(x_175);
x_598 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_599 = lean_nat_dec_lt(x_580, x_579);
if (x_599 == 0)
{
lean_dec(x_579);
x_583 = x_598;
x_584 = x_576;
goto block_597;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_600 = l_Lean_IR_instInhabitedArg;
x_601 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_578, x_600, x_582, x_579, x_598, x_580, x_576);
lean_dec(x_579);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec_ref(x_601);
x_583 = x_602;
x_584 = x_603;
goto block_597;
}
block_597:
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_585 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_584);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_588 = x_585;
} else {
 lean_dec_ref(x_585);
 x_588 = lean_box(0);
}
lean_inc(x_586);
x_589 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_577, x_578, x_582, x_586, x_3, x_4, x_5, x_587);
lean_dec_ref(x_582);
lean_dec_ref(x_578);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_592 = x_589;
} else {
 lean_dec_ref(x_589);
 x_592 = lean_box(0);
}
x_593 = l_Lean_IR_CtorInfo_type(x_577);
if (lean_is_scalar(x_588)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_588;
}
lean_ctor_set(x_594, 0, x_577);
lean_ctor_set(x_594, 1, x_583);
if (lean_is_scalar(x_566)) {
 x_595 = lean_alloc_ctor(0, 4, 0);
} else {
 x_595 = x_566;
}
lean_ctor_set(x_595, 0, x_586);
lean_ctor_set(x_595, 1, x_593);
lean_ctor_set(x_595, 2, x_594);
lean_ctor_set(x_595, 3, x_590);
if (lean_is_scalar(x_592)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_592;
}
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_591);
return x_596;
}
else
{
lean_dec(x_588);
lean_dec(x_586);
lean_dec_ref(x_583);
lean_dec_ref(x_577);
lean_dec(x_566);
return x_589;
}
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_175);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_604 = lean_ctor_get(x_574, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_574, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_606 = x_574;
} else {
 lean_dec_ref(x_574);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_569);
lean_dec(x_175);
lean_dec(x_169);
x_608 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_572);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec_ref(x_608);
x_611 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_610);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_614 = x_611;
} else {
 lean_dec_ref(x_611);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_615 = lean_alloc_ctor(0, 1, 0);
} else {
 x_615 = x_564;
 lean_ctor_set_tag(x_615, 0);
}
lean_ctor_set(x_615, 0, x_568);
if (lean_is_scalar(x_522)) {
 x_616 = lean_alloc_ctor(11, 1, 0);
} else {
 x_616 = x_522;
 lean_ctor_set_tag(x_616, 11);
}
lean_ctor_set(x_616, 0, x_615);
if (lean_is_scalar(x_566)) {
 x_617 = lean_alloc_ctor(0, 4, 0);
} else {
 x_617 = x_566;
}
lean_ctor_set(x_617, 0, x_609);
lean_ctor_set(x_617, 1, x_571);
lean_ctor_set(x_617, 2, x_616);
lean_ctor_set(x_617, 3, x_612);
if (lean_is_scalar(x_614)) {
 x_618 = lean_alloc_ctor(0, 2, 0);
} else {
 x_618 = x_614;
}
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_613);
return x_618;
}
else
{
lean_dec(x_609);
lean_dec(x_571);
lean_dec(x_568);
lean_dec(x_566);
lean_dec(x_564);
lean_dec(x_522);
return x_611;
}
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_566);
lean_dec(x_564);
lean_dec(x_522);
lean_dec(x_175);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_619 = lean_ctor_get(x_570, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_570, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_621 = x_570;
} else {
 lean_dec_ref(x_570);
 x_621 = lean_box(0);
}
if (lean_is_scalar(x_621)) {
 x_622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_622 = x_621;
}
lean_ctor_set(x_622, 0, x_619);
lean_ctor_set(x_622, 1, x_620);
return x_622;
}
}
else
{
lean_object* x_623; 
lean_dec(x_564);
lean_dec_ref(x_563);
lean_dec(x_522);
x_623 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_175, x_3, x_4, x_5, x_515);
return x_623;
}
}
case 7:
{
lean_object* x_624; lean_object* x_625; uint8_t x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_522);
lean_dec_ref(x_516);
lean_dec(x_175);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_624 = x_521;
} else {
 lean_dec_ref(x_521);
 x_624 = lean_box(0);
}
x_625 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_626 = 1;
x_627 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_626);
if (lean_is_scalar(x_624)) {
 x_628 = lean_alloc_ctor(3, 1, 0);
} else {
 x_628 = x_624;
 lean_ctor_set_tag(x_628, 3);
}
lean_ctor_set(x_628, 0, x_627);
x_629 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_629, 0, x_625);
lean_ctor_set(x_629, 1, x_628);
x_630 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_630);
lean_ctor_set(x_173, 0, x_629);
x_631 = l_Lean_MessageData_ofFormat(x_173);
x_632 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_631, x_4, x_5, x_515);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_632;
}
default: 
{
lean_object* x_633; 
lean_dec(x_522);
lean_dec(x_521);
lean_dec_ref(x_516);
lean_free_object(x_173);
x_633 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_175, x_3, x_4, x_5, x_515);
return x_633;
}
}
}
}
}
else
{
uint8_t x_634; 
lean_free_object(x_173);
lean_dec(x_175);
lean_dec(x_169);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_634 = !lean_is_exclusive(x_177);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; 
x_635 = lean_ctor_get(x_177, 0);
lean_dec(x_635);
x_636 = lean_ctor_get(x_178, 0);
lean_inc(x_636);
lean_dec_ref(x_178);
lean_ctor_set(x_177, 0, x_636);
return x_177;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_177, 1);
lean_inc(x_637);
lean_dec(x_177);
x_638 = lean_ctor_get(x_178, 0);
lean_inc(x_638);
lean_dec_ref(x_178);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
}
else
{
uint8_t x_640; 
lean_free_object(x_173);
lean_dec(x_175);
lean_dec(x_169);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_640 = !lean_is_exclusive(x_177);
if (x_640 == 0)
{
return x_177;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_177, 0);
x_642 = lean_ctor_get(x_177, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_177);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_173, 0);
x_645 = lean_ctor_get(x_173, 1);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_173);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_644);
lean_inc(x_169);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_646 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_169, x_644, x_3, x_4, x_5, x_645);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; lean_object* x_655; 
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
lean_dec_ref(x_646);
x_649 = lean_st_ref_get(x_5, x_648);
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_652 = x_649;
} else {
 lean_dec_ref(x_649);
 x_652 = lean_box(0);
}
x_653 = lean_ctor_get(x_650, 0);
lean_inc_ref(x_653);
lean_dec(x_650);
x_654 = 0;
lean_inc(x_169);
lean_inc_ref(x_653);
x_655 = l_Lean_Environment_find_x3f(x_653, x_169, x_654);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; 
lean_dec_ref(x_653);
lean_dec(x_652);
lean_dec(x_644);
lean_dec(x_169);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_656 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_657 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_656, x_3, x_4, x_5, x_651);
return x_657;
}
else
{
lean_object* x_658; lean_object* x_659; 
x_658 = lean_ctor_get(x_655, 0);
lean_inc(x_658);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 x_659 = x_655;
} else {
 lean_dec_ref(x_655);
 x_659 = lean_box(0);
}
switch (lean_obj_tag(x_658)) {
case 0:
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_659);
lean_dec_ref(x_653);
lean_dec(x_644);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 x_660 = x_658;
} else {
 lean_dec_ref(x_658);
 x_660 = lean_box(0);
}
x_661 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_662 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_663 = 1;
x_664 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_663);
if (lean_is_scalar(x_660)) {
 x_665 = lean_alloc_ctor(3, 1, 0);
} else {
 x_665 = x_660;
 lean_ctor_set_tag(x_665, 3);
}
lean_ctor_set(x_665, 0, x_664);
if (lean_is_scalar(x_652)) {
 x_666 = lean_alloc_ctor(5, 2, 0);
} else {
 x_666 = x_652;
 lean_ctor_set_tag(x_666, 5);
}
lean_ctor_set(x_666, 0, x_662);
lean_ctor_set(x_666, 1, x_665);
x_667 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_668 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
x_669 = l_Lean_MessageData_ofFormat(x_668);
x_670 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_661, x_669, x_4, x_5, x_651);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_670;
}
case 2:
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_659);
lean_dec_ref(x_653);
lean_dec(x_644);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 x_671 = x_658;
} else {
 lean_dec_ref(x_658);
 x_671 = lean_box(0);
}
x_672 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_673 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_674 = 1;
x_675 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_674);
if (lean_is_scalar(x_671)) {
 x_676 = lean_alloc_ctor(3, 1, 0);
} else {
 x_676 = x_671;
 lean_ctor_set_tag(x_676, 3);
}
lean_ctor_set(x_676, 0, x_675);
if (lean_is_scalar(x_652)) {
 x_677 = lean_alloc_ctor(5, 2, 0);
} else {
 x_677 = x_652;
 lean_ctor_set_tag(x_677, 5);
}
lean_ctor_set(x_677, 0, x_673);
lean_ctor_set(x_677, 1, x_676);
x_678 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_679 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
x_680 = l_Lean_MessageData_ofFormat(x_679);
x_681 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_672, x_680, x_4, x_5, x_651);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_681;
}
case 4:
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
lean_dec(x_659);
lean_dec_ref(x_653);
lean_dec(x_644);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 x_682 = x_658;
} else {
 lean_dec_ref(x_658);
 x_682 = lean_box(0);
}
x_683 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_684 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_685 = 1;
x_686 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_685);
if (lean_is_scalar(x_682)) {
 x_687 = lean_alloc_ctor(3, 1, 0);
} else {
 x_687 = x_682;
 lean_ctor_set_tag(x_687, 3);
}
lean_ctor_set(x_687, 0, x_686);
if (lean_is_scalar(x_652)) {
 x_688 = lean_alloc_ctor(5, 2, 0);
} else {
 x_688 = x_652;
 lean_ctor_set_tag(x_688, 5);
}
lean_ctor_set(x_688, 0, x_684);
lean_ctor_set(x_688, 1, x_687);
x_689 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_690 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_690, 0, x_688);
lean_ctor_set(x_690, 1, x_689);
x_691 = l_Lean_MessageData_ofFormat(x_690);
x_692 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_683, x_691, x_4, x_5, x_651);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_692;
}
case 5:
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_659);
lean_dec_ref(x_653);
lean_dec(x_644);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 x_693 = x_658;
} else {
 lean_dec_ref(x_658);
 x_693 = lean_box(0);
}
x_694 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_695 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_696 = 1;
x_697 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_696);
if (lean_is_scalar(x_693)) {
 x_698 = lean_alloc_ctor(3, 1, 0);
} else {
 x_698 = x_693;
 lean_ctor_set_tag(x_698, 3);
}
lean_ctor_set(x_698, 0, x_697);
if (lean_is_scalar(x_652)) {
 x_699 = lean_alloc_ctor(5, 2, 0);
} else {
 x_699 = x_652;
 lean_ctor_set_tag(x_699, 5);
}
lean_ctor_set(x_699, 0, x_695);
lean_ctor_set(x_699, 1, x_698);
x_700 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_701 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_701, 0, x_699);
lean_ctor_set(x_701, 1, x_700);
x_702 = l_Lean_MessageData_ofFormat(x_701);
x_703 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_694, x_702, x_4, x_5, x_651);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_703;
}
case 6:
{
lean_object* x_704; lean_object* x_705; uint8_t x_706; 
lean_dec(x_652);
x_704 = lean_ctor_get(x_658, 0);
lean_inc_ref(x_704);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 x_705 = x_658;
} else {
 lean_dec_ref(x_658);
 x_705 = lean_box(0);
}
lean_inc(x_169);
x_706 = l_Lean_isExtern(x_653, x_169);
if (x_706 == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_707 = x_1;
} else {
 lean_dec_ref(x_1);
 x_707 = lean_box(0);
}
x_708 = lean_ctor_get(x_704, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_704, 2);
lean_inc(x_709);
x_710 = lean_ctor_get(x_704, 3);
lean_inc(x_710);
lean_dec_ref(x_704);
lean_inc(x_5);
lean_inc_ref(x_4);
x_711 = l_Lean_IR_nameToIRType(x_708, x_4, x_5, x_651);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; uint8_t x_714; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec_ref(x_711);
x_714 = l_Lean_IR_IRType_isScalar(x_712);
if (x_714 == 0)
{
lean_object* x_715; 
lean_dec(x_712);
lean_dec(x_709);
lean_dec(x_705);
lean_dec(x_659);
lean_inc(x_5);
lean_inc_ref(x_4);
x_715 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_713);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_739; uint8_t x_740; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec_ref(x_715);
x_718 = lean_ctor_get(x_716, 0);
lean_inc_ref(x_718);
x_719 = lean_ctor_get(x_716, 1);
lean_inc_ref(x_719);
lean_dec(x_716);
x_720 = lean_array_get_size(x_719);
x_721 = lean_unsigned_to_nat(0u);
x_722 = lean_array_get_size(x_644);
x_723 = l_Array_extract___redArg(x_644, x_710, x_722);
lean_dec(x_644);
x_739 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_740 = lean_nat_dec_lt(x_721, x_720);
if (x_740 == 0)
{
lean_dec(x_720);
x_724 = x_739;
x_725 = x_717;
goto block_738;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_741 = l_Lean_IR_instInhabitedArg;
x_742 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_719, x_741, x_723, x_720, x_739, x_721, x_717);
lean_dec(x_720);
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
lean_dec_ref(x_742);
x_724 = x_743;
x_725 = x_744;
goto block_738;
}
block_738:
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_726 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_725);
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_729 = x_726;
} else {
 lean_dec_ref(x_726);
 x_729 = lean_box(0);
}
lean_inc(x_727);
x_730 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_718, x_719, x_723, x_727, x_3, x_4, x_5, x_728);
lean_dec_ref(x_723);
lean_dec_ref(x_719);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_733 = x_730;
} else {
 lean_dec_ref(x_730);
 x_733 = lean_box(0);
}
x_734 = l_Lean_IR_CtorInfo_type(x_718);
if (lean_is_scalar(x_729)) {
 x_735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_735 = x_729;
}
lean_ctor_set(x_735, 0, x_718);
lean_ctor_set(x_735, 1, x_724);
if (lean_is_scalar(x_707)) {
 x_736 = lean_alloc_ctor(0, 4, 0);
} else {
 x_736 = x_707;
}
lean_ctor_set(x_736, 0, x_727);
lean_ctor_set(x_736, 1, x_734);
lean_ctor_set(x_736, 2, x_735);
lean_ctor_set(x_736, 3, x_731);
if (lean_is_scalar(x_733)) {
 x_737 = lean_alloc_ctor(0, 2, 0);
} else {
 x_737 = x_733;
}
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_732);
return x_737;
}
else
{
lean_dec(x_729);
lean_dec(x_727);
lean_dec_ref(x_724);
lean_dec_ref(x_718);
lean_dec(x_707);
return x_730;
}
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_dec(x_710);
lean_dec(x_707);
lean_dec(x_644);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_745 = lean_ctor_get(x_715, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_715, 1);
lean_inc(x_746);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_747 = x_715;
} else {
 lean_dec_ref(x_715);
 x_747 = lean_box(0);
}
if (lean_is_scalar(x_747)) {
 x_748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_748 = x_747;
}
lean_ctor_set(x_748, 0, x_745);
lean_ctor_set(x_748, 1, x_746);
return x_748;
}
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_710);
lean_dec(x_644);
lean_dec(x_169);
x_749 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_713);
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
lean_dec_ref(x_749);
x_752 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_751);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_755 = x_752;
} else {
 lean_dec_ref(x_752);
 x_755 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_756 = lean_alloc_ctor(0, 1, 0);
} else {
 x_756 = x_705;
 lean_ctor_set_tag(x_756, 0);
}
lean_ctor_set(x_756, 0, x_709);
if (lean_is_scalar(x_659)) {
 x_757 = lean_alloc_ctor(11, 1, 0);
} else {
 x_757 = x_659;
 lean_ctor_set_tag(x_757, 11);
}
lean_ctor_set(x_757, 0, x_756);
if (lean_is_scalar(x_707)) {
 x_758 = lean_alloc_ctor(0, 4, 0);
} else {
 x_758 = x_707;
}
lean_ctor_set(x_758, 0, x_750);
lean_ctor_set(x_758, 1, x_712);
lean_ctor_set(x_758, 2, x_757);
lean_ctor_set(x_758, 3, x_753);
if (lean_is_scalar(x_755)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_755;
}
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_754);
return x_759;
}
else
{
lean_dec(x_750);
lean_dec(x_712);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_705);
lean_dec(x_659);
return x_752;
}
}
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_705);
lean_dec(x_659);
lean_dec(x_644);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_760 = lean_ctor_get(x_711, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_711, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_762 = x_711;
} else {
 lean_dec_ref(x_711);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(1, 2, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_760);
lean_ctor_set(x_763, 1, x_761);
return x_763;
}
}
else
{
lean_object* x_764; 
lean_dec(x_705);
lean_dec_ref(x_704);
lean_dec(x_659);
x_764 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_644, x_3, x_4, x_5, x_651);
return x_764;
}
}
case 7:
{
lean_object* x_765; lean_object* x_766; uint8_t x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_659);
lean_dec_ref(x_653);
lean_dec(x_644);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 x_765 = x_658;
} else {
 lean_dec_ref(x_658);
 x_765 = lean_box(0);
}
x_766 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_767 = 1;
x_768 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_169, x_767);
if (lean_is_scalar(x_765)) {
 x_769 = lean_alloc_ctor(3, 1, 0);
} else {
 x_769 = x_765;
 lean_ctor_set_tag(x_769, 3);
}
lean_ctor_set(x_769, 0, x_768);
if (lean_is_scalar(x_652)) {
 x_770 = lean_alloc_ctor(5, 2, 0);
} else {
 x_770 = x_652;
 lean_ctor_set_tag(x_770, 5);
}
lean_ctor_set(x_770, 0, x_766);
lean_ctor_set(x_770, 1, x_769);
x_771 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_772 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
x_773 = l_Lean_MessageData_ofFormat(x_772);
x_774 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_773, x_4, x_5, x_651);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_774;
}
default: 
{
lean_object* x_775; 
lean_dec(x_659);
lean_dec(x_658);
lean_dec_ref(x_653);
lean_dec(x_652);
x_775 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_644, x_3, x_4, x_5, x_651);
return x_775;
}
}
}
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
lean_dec(x_644);
lean_dec(x_169);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_776 = lean_ctor_get(x_646, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_777 = x_646;
} else {
 lean_dec_ref(x_646);
 x_777 = lean_box(0);
}
x_778 = lean_ctor_get(x_647, 0);
lean_inc(x_778);
lean_dec_ref(x_647);
if (lean_is_scalar(x_777)) {
 x_779 = lean_alloc_ctor(0, 2, 0);
} else {
 x_779 = x_777;
}
lean_ctor_set(x_779, 0, x_778);
lean_ctor_set(x_779, 1, x_776);
return x_779;
}
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_644);
lean_dec(x_169);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_780 = lean_ctor_get(x_646, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_646, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_782 = x_646;
} else {
 lean_dec_ref(x_646);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(1, 2, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_780);
lean_ctor_set(x_783, 1, x_781);
return x_783;
}
}
}
default: 
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_784 = lean_ctor_get(x_14, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_785);
lean_dec_ref(x_14);
x_786 = l_Lean_IR_ToIR_getFVarValue___redArg(x_784, x_3, x_6);
lean_dec(x_784);
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; size_t x_790; size_t x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec_ref(x_786);
x_789 = lean_ctor_get(x_787, 0);
lean_inc(x_789);
lean_dec_ref(x_787);
x_790 = lean_array_size(x_785);
x_791 = 0;
x_792 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_790, x_791, x_785, x_3, x_788);
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec_ref(x_792);
x_795 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(x_1, x_2, x_789, x_793, x_3, x_4, x_5, x_794);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; 
lean_dec_ref(x_785);
x_796 = lean_ctor_get(x_786, 1);
lean_inc(x_796);
lean_dec_ref(x_786);
x_797 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_796);
return x_797;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_IR_ToIR_lowerLet___closed__2;
x_12 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_ToIR_bindErased___redArg(x_7, x_3, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
x_18 = l_Lean_IR_toIRType(x_11, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_IR_IRType_boxed(x_19);
lean_dec(x_19);
lean_ctor_set_tag(x_14, 8);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l_Lean_IR_IRType_boxed(x_19);
lean_dec(x_19);
lean_ctor_set_tag(x_14, 8);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_1, 3, x_25);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_dec(x_19);
lean_free_object(x_14);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_21;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_14);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
x_35 = l_Lean_IR_toIRType(x_11, x_6, x_7, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l_Lean_IR_IRType_boxed(x_36);
lean_dec(x_36);
x_43 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_4);
lean_ctor_set(x_1, 3, x_39);
lean_ctor_set(x_1, 2, x_43);
lean_ctor_set(x_1, 1, x_42);
lean_ctor_set(x_1, 0, x_33);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_dec(x_36);
lean_dec(x_33);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_38;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_33);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_51 = l_Lean_IR_ToIR_bindVar___redArg(x_49, x_5, x_8);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
lean_inc(x_7);
lean_inc_ref(x_6);
x_55 = l_Lean_IR_toIRType(x_50, x_6, x_7, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = l_Lean_IR_IRType_boxed(x_56);
lean_dec(x_56);
if (lean_is_scalar(x_54)) {
 x_63 = lean_alloc_ctor(8, 2, 0);
} else {
 x_63 = x_54;
 lean_ctor_set_tag(x_63, 8);
}
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_4);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_59);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
else
{
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_52);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_58;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_68 = x_55;
} else {
 lean_dec_ref(x_55);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
x_18 = l_Lean_IR_toIRType(x_11, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set_tag(x_14, 6);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set_tag(x_14, 6);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_1, 3, x_24);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_dec(x_19);
lean_free_object(x_14);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_21;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
x_33 = l_Lean_IR_toIRType(x_11, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_4);
lean_ctor_set(x_1, 3, x_37);
lean_ctor_set(x_1, 2, x_40);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_dec(x_34);
lean_dec(x_31);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_36;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_48 = l_Lean_IR_ToIR_bindVar___redArg(x_46, x_5, x_8);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
lean_inc(x_7);
lean_inc_ref(x_6);
x_52 = l_Lean_IR_toIRType(x_47, x_6, x_7, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_59 = lean_alloc_ctor(6, 2, 0);
} else {
 x_59 = x_51;
 lean_ctor_set_tag(x_59, 6);
}
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_4);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_56);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
else
{
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_49);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_55;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_64 = x_52;
} else {
 lean_dec_ref(x_52);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
x_13 = l_Lean_IR_ToIR_lowerCode(x_1, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fget_borrowed(x_4, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_box(0);
x_17 = lean_array_get_borrowed(x_16, x_3, x_6);
switch (lean_obj_tag(x_17)) {
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
lean_inc(x_5);
x_21 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_15);
lean_inc(x_18);
x_24 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
lean_inc(x_15);
lean_inc(x_18);
x_27 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_15);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_dec(x_5);
return x_21;
}
}
case 3:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_17, 1);
x_30 = lean_ctor_get(x_17, 2);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_6, x_31);
lean_dec(x_6);
lean_inc(x_5);
x_33 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_32, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = lean_nat_add(x_36, x_37);
lean_inc(x_30);
lean_inc(x_15);
lean_inc(x_29);
x_39 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_29);
lean_ctor_set(x_39, 3, x_15);
lean_ctor_set(x_39, 4, x_30);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_2, 3);
x_44 = lean_nat_add(x_42, x_43);
lean_inc(x_30);
lean_inc(x_15);
lean_inc(x_29);
x_45 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_29);
lean_ctor_set(x_45, 3, x_15);
lean_ctor_set(x_45, 4, x_30);
lean_ctor_set(x_45, 5, x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
else
{
lean_dec(x_5);
return x_33;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_6, x_47);
lean_dec(x_6);
x_6 = x_48;
goto _start;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_6, x_50);
lean_dec(x_6);
x_6 = x_51;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_3);
x_9 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_3, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec_ref(x_9);
x_20 = lean_ctor_get(x_18, 3);
lean_inc_ref(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_4);
x_22 = lean_array_get_size(x_20);
lean_dec_ref(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_22, x_4, x_5, x_6, x_7, x_19);
lean_dec_ref(x_4);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_10, 0, x_27);
lean_ctor_set(x_25, 0, x_10);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_10, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_10);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_22);
x_35 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_10, 0, x_37);
lean_ctor_set(x_35, 0, x_10);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_10, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_10);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_22);
lean_dec(x_21);
x_45 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_10, 0, x_47);
lean_ctor_set(x_45, 0, x_10);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_10, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_10);
x_51 = !lean_is_exclusive(x_45);
if (x_51 == 0)
{
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_10, 0);
lean_inc(x_55);
lean_dec(x_10);
x_56 = lean_ctor_get(x_9, 1);
lean_inc(x_56);
lean_dec_ref(x_9);
x_57 = lean_ctor_get(x_55, 3);
lean_inc_ref(x_57);
lean_dec(x_55);
x_58 = lean_array_get_size(x_4);
x_59 = lean_array_get_size(x_57);
lean_dec_ref(x_57);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_59, x_4, x_5, x_6, x_7, x_56);
lean_dec_ref(x_4);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_63);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_59);
x_72 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_59);
lean_dec(x_58);
x_82 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_9);
if (x_92 == 0)
{
return x_9;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_9, 0);
x_94 = lean_ctor_get(x_9, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_9);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = l_Lean_IR_ToIR_bindVar___redArg(x_11, x_6, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
x_19 = l_Lean_IR_toIRType(x_12, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_IR_ToIR_newVar___redArg(x_6, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_IR_ToIR_lowerCode(x_2, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_IR_IRType_boxed(x_20);
lean_dec(x_20);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_31 = l_Array_extract___redArg(x_5, x_30, x_4);
x_32 = lean_array_get_size(x_5);
x_33 = l_Array_extract___redArg(x_5, x_4, x_32);
x_34 = lean_box(7);
lean_ctor_set_tag(x_22, 6);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_3);
lean_inc(x_24);
lean_ctor_set_tag(x_15, 8);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_15, 0, x_24);
lean_ctor_set(x_1, 3, x_28);
lean_ctor_set(x_1, 2, x_15);
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_17);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_35, 3, x_1);
lean_ctor_set(x_26, 0, x_35);
return x_26;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
x_38 = l_Lean_IR_IRType_boxed(x_20);
lean_dec(x_20);
x_39 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_40 = l_Array_extract___redArg(x_5, x_39, x_4);
x_41 = lean_array_get_size(x_5);
x_42 = l_Array_extract___redArg(x_5, x_4, x_41);
x_43 = lean_box(7);
lean_ctor_set_tag(x_22, 6);
lean_ctor_set(x_22, 1, x_40);
lean_ctor_set(x_22, 0, x_3);
lean_inc(x_24);
lean_ctor_set_tag(x_15, 8);
lean_ctor_set(x_15, 1, x_42);
lean_ctor_set(x_15, 0, x_24);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_15);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_17);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_22);
lean_ctor_set(x_44, 3, x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
}
else
{
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_20);
lean_free_object(x_15);
lean_dec(x_17);
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_22, 0);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_22);
x_48 = l_Lean_IR_ToIR_lowerCode(x_2, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = l_Lean_IR_IRType_boxed(x_20);
lean_dec(x_20);
x_53 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_54 = l_Array_extract___redArg(x_5, x_53, x_4);
x_55 = lean_array_get_size(x_5);
x_56 = l_Array_extract___redArg(x_5, x_4, x_55);
x_57 = lean_box(7);
x_58 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_58, 0, x_3);
lean_ctor_set(x_58, 1, x_54);
lean_inc(x_46);
lean_ctor_set_tag(x_15, 8);
lean_ctor_set(x_15, 1, x_56);
lean_ctor_set(x_15, 0, x_46);
lean_ctor_set(x_1, 3, x_49);
lean_ctor_set(x_1, 2, x_15);
lean_ctor_set(x_1, 1, x_52);
lean_ctor_set(x_1, 0, x_17);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_46);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_1);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
else
{
lean_dec(x_46);
lean_dec(x_20);
lean_free_object(x_15);
lean_dec(x_17);
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
return x_48;
}
}
}
else
{
uint8_t x_61; 
lean_free_object(x_15);
lean_dec(x_17);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
return x_19;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
lean_inc(x_8);
lean_inc_ref(x_7);
x_67 = l_Lean_IR_toIRType(x_12, x_7, x_8, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = l_Lean_IR_ToIR_newVar___redArg(x_6, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = l_Lean_IR_ToIR_lowerCode(x_2, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = l_Lean_IR_IRType_boxed(x_68);
lean_dec(x_68);
x_79 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_80 = l_Array_extract___redArg(x_5, x_79, x_4);
x_81 = lean_array_get_size(x_5);
x_82 = l_Array_extract___redArg(x_5, x_4, x_81);
x_83 = lean_box(7);
if (lean_is_scalar(x_73)) {
 x_84 = lean_alloc_ctor(6, 2, 0);
} else {
 x_84 = x_73;
 lean_ctor_set_tag(x_84, 6);
}
lean_ctor_set(x_84, 0, x_3);
lean_ctor_set(x_84, 1, x_80);
lean_inc(x_71);
x_85 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set(x_1, 3, x_75);
lean_ctor_set(x_1, 2, x_85);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_65);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_86, 1, x_83);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set(x_86, 3, x_1);
if (lean_is_scalar(x_77)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_77;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
return x_87;
}
else
{
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_65);
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
return x_74;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_65);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_88 = lean_ctor_get(x_67, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_90 = x_67;
} else {
 lean_dec_ref(x_67);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_1, 0);
x_93 = lean_ctor_get(x_1, 2);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_1);
x_94 = l_Lean_IR_ToIR_bindVar___redArg(x_92, x_6, x_9);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
x_98 = l_Lean_IR_toIRType(x_93, x_7, x_8, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = l_Lean_IR_ToIR_newVar___redArg(x_6, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = l_Lean_IR_ToIR_lowerCode(x_2, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = l_Lean_IR_IRType_boxed(x_99);
lean_dec(x_99);
x_110 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_111 = l_Array_extract___redArg(x_5, x_110, x_4);
x_112 = lean_array_get_size(x_5);
x_113 = l_Array_extract___redArg(x_5, x_4, x_112);
x_114 = lean_box(7);
if (lean_is_scalar(x_104)) {
 x_115 = lean_alloc_ctor(6, 2, 0);
} else {
 x_115 = x_104;
 lean_ctor_set_tag(x_115, 6);
}
lean_ctor_set(x_115, 0, x_3);
lean_ctor_set(x_115, 1, x_111);
lean_inc(x_102);
if (lean_is_scalar(x_97)) {
 x_116 = lean_alloc_ctor(8, 2, 0);
} else {
 x_116 = x_97;
 lean_ctor_set_tag(x_116, 8);
}
lean_ctor_set(x_116, 0, x_102);
lean_ctor_set(x_116, 1, x_113);
x_117 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_117, 0, x_95);
lean_ctor_set(x_117, 1, x_109);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_106);
x_118 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_118, 0, x_102);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 3, x_117);
if (lean_is_scalar(x_108)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_108;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_107);
return x_119;
}
else
{
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_3);
return x_105;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_120 = lean_ctor_get(x_98, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_98, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_122 = x_98;
} else {
 lean_dec_ref(x_98);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_box(7);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_1, 3, x_20);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_box(7);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_1, 3, x_22);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_free_object(x_14);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_box(7);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_4);
lean_ctor_set(x_1, 3, x_29);
lean_ctor_set(x_1, 2, x_33);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_26);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
lean_dec(x_26);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_28;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_5, x_8);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_box(7);
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(7, 2, 0);
} else {
 x_45 = x_39;
 lean_ctor_set_tag(x_45, 7);
}
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_4);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_41);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
lean_dec(x_39);
lean_dec(x_37);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ToIR_lowerCode_spec__3(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_4);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_8, x_3, x_4, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_ToIR_lowerCode(x_2, x_4, x_5, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerResultType.resultTypeForArity", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid arity", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(299u);
x_4 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
goto block_5;
}
else
{
lean_object* x_13; 
x_13 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
return x_13;
}
}
else
{
goto block_5;
}
}
else
{
goto block_5;
}
}
case 7:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_1 = x_14;
x_2 = x_16;
goto _start;
}
default: 
{
lean_dec(x_2);
goto block_5;
}
}
}
else
{
lean_dec(x_2);
lean_inc_ref(x_1);
return x_1;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
x_4 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity_spec__0(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
x_7 = l_Lean_IR_toIRType(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerResultType___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_array_size(x_8);
x_11 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_8);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_10, x_11, x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
lean_inc(x_4);
lean_inc_ref(x_3);
x_16 = l_Lean_IR_ToIR_lowerResultType___redArg(x_7, x_15, x_3, x_4, x_14);
lean_dec_ref(x_7);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = l_Lean_IR_ToIR_lowerCode(x_20, x_2, x_3, x_4, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_9);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
lean_dec(x_9);
x_36 = l_Lean_IR_ToIR_lowerCode(x_35, x_2, x_3, x_4, x_18);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_13);
lean_ctor_set(x_41, 2, x_17);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_6);
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_46 = x_36;
} else {
 lean_dec_ref(x_36);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_9);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
x_52 = lean_ctor_get(x_9, 0);
x_53 = l_List_isEmpty___redArg(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_4);
x_54 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_13);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set(x_9, 0, x_54);
lean_ctor_set(x_16, 0, x_9);
return x_16;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_free_object(x_9);
lean_dec(x_52);
lean_free_object(x_16);
x_55 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_50);
x_56 = l_Lean_IR_ToIR_addDecl___redArg(x_55, x_4, x_51);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_16, 0);
x_64 = lean_ctor_get(x_16, 1);
x_65 = lean_ctor_get(x_9, 0);
lean_inc(x_65);
lean_dec(x_9);
x_66 = l_List_isEmpty___redArg(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_4);
x_67 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_67, 0, x_6);
lean_ctor_set(x_67, 1, x_13);
lean_ctor_set(x_67, 2, x_63);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_16, 0, x_68);
return x_16;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_65);
lean_free_object(x_16);
x_69 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_63);
x_70 = l_Lean_IR_ToIR_addDecl___redArg(x_69, x_4, x_64);
lean_dec(x_4);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_16, 0);
x_76 = lean_ctor_get(x_16, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_16);
x_77 = lean_ctor_get(x_9, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_78 = x_9;
} else {
 lean_dec_ref(x_9);
 x_78 = lean_box(0);
}
x_79 = l_List_isEmpty___redArg(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_4);
x_80 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_80, 0, x_6);
lean_ctor_set(x_80, 1, x_13);
lean_ctor_set(x_80, 2, x_75);
lean_ctor_set(x_80, 3, x_77);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_78);
lean_dec(x_77);
x_83 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_75);
x_84 = l_Lean_IR_ToIR_addDecl___redArg(x_83, x_4, x_76);
lean_dec(x_4);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_16);
if (x_89 == 0)
{
return x_16;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_16, 0);
x_91 = lean_ctor_get(x_16, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_16);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_12);
if (x_93 == 0)
{
return x_12;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_12, 0);
x_95 = lean_ctor_get(x_12, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_12);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl), 5, 1);
lean_closure_set(x_11, 0, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_IR_ToIR_M_run___redArg(x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 0)
{
x_15 = x_4;
goto block_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec_ref(x_13);
x_21 = lean_array_push(x_4, x_20);
x_15 = x_21;
goto block_19;
}
block_19:
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_15;
x_7 = x_14;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_toIR___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = l_Lean_IR_toIR___closed__0;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(x_1, x_6, x_7, x_5, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_toIR(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ToIR_M_run___redArg___closed__0 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__0);
l_Lean_IR_ToIR_M_run___redArg___closed__1 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__1);
l_Lean_IR_ToIR_M_run___redArg___closed__2 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__2);
l_Lean_IR_ToIR_M_run___redArg___closed__3 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__3);
l_Lean_IR_ToIR_M_run___redArg___closed__4 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__4);
l_Lean_IR_ToIR_M_run___redArg___closed__5 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__5);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__0 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__0);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__1 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__1();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__1);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__2 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__2();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___closed__3);
l_Lean_IR_ToIR_addDecl___redArg___closed__0 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__0);
l_Lean_IR_ToIR_addDecl___redArg___closed__1 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__1);
l_Lean_IR_ToIR_addDecl___redArg___closed__2 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__2);
l_Lean_IR_ToIR_addDecl___redArg___closed__3 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__3);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3);
l_Lean_IR_ToIR_instInhabitedTranslatedProj = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj);
l_Lean_IR_ToIR_lowerProj___closed__0 = _init_l_Lean_IR_ToIR_lowerProj___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerProj___closed__0);
l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0 = _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0();
lean_mark_persistent(l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0);
l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1 = _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1();
lean_mark_persistent(l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1);
l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2 = _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2();
lean_mark_persistent(l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3);
l_Lean_IR_ToIR_lowerCode___closed__0 = _init_l_Lean_IR_ToIR_lowerCode___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__0);
l_Lean_IR_ToIR_lowerCode___closed__1 = _init_l_Lean_IR_ToIR_lowerCode___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__1);
l_Lean_IR_ToIR_lowerCode___closed__2 = _init_l_Lean_IR_ToIR_lowerCode___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__2);
l_Lean_IR_ToIR_lowerCode___closed__3 = _init_l_Lean_IR_ToIR_lowerCode___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__3);
l_Lean_IR_ToIR_lowerCode___closed__4 = _init_l_Lean_IR_ToIR_lowerCode___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__4);
l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__0 = _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__0);
l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1 = _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1);
l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2 = _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2);
l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3 = _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3);
l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4 = _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4);
l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__5 = _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__5);
l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6 = _init_l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6);
l_Lean_IR_ToIR_lowerLet___closed__0 = _init_l_Lean_IR_ToIR_lowerLet___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__0);
l_Lean_IR_ToIR_lowerLet___closed__1 = _init_l_Lean_IR_ToIR_lowerLet___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__1);
l_Lean_IR_ToIR_lowerLet___closed__2 = _init_l_Lean_IR_ToIR_lowerLet___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__2);
l_Lean_IR_ToIR_lowerLet___closed__3 = _init_l_Lean_IR_ToIR_lowerLet___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__3);
l_Lean_IR_ToIR_lowerLet___closed__4 = _init_l_Lean_IR_ToIR_lowerLet___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__4);
l_Lean_IR_ToIR_lowerLet___closed__5 = _init_l_Lean_IR_ToIR_lowerLet___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__5);
l_Lean_IR_ToIR_lowerLet___closed__6 = _init_l_Lean_IR_ToIR_lowerLet___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__6);
l_Lean_IR_ToIR_lowerLet___closed__7 = _init_l_Lean_IR_ToIR_lowerLet___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__7);
l_Lean_IR_ToIR_lowerLet___closed__8 = _init_l_Lean_IR_ToIR_lowerLet___closed__8();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__8);
l_Lean_IR_ToIR_lowerLet___closed__9 = _init_l_Lean_IR_ToIR_lowerLet___closed__9();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__9);
l_Lean_IR_ToIR_lowerLet___closed__10 = _init_l_Lean_IR_ToIR_lowerLet___closed__10();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__10);
l_Lean_IR_ToIR_lowerLet___closed__11 = _init_l_Lean_IR_ToIR_lowerLet___closed__11();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__11);
l_Lean_IR_ToIR_lowerLet___closed__12 = _init_l_Lean_IR_ToIR_lowerLet___closed__12();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__12);
l_Lean_IR_ToIR_lowerLet___closed__13 = _init_l_Lean_IR_ToIR_lowerLet___closed__13();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__13);
l_Lean_IR_ToIR_lowerLet___closed__14 = _init_l_Lean_IR_ToIR_lowerLet___closed__14();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__14);
l_Lean_IR_ToIR_lowerLet___closed__15 = _init_l_Lean_IR_ToIR_lowerLet___closed__15();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__15);
l_Lean_IR_ToIR_lowerLet___closed__16 = _init_l_Lean_IR_ToIR_lowerLet___closed__16();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__16);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5);
l_Lean_IR_toIR___closed__0 = _init_l_Lean_IR_toIR___closed__0();
lean_mark_persistent(l_Lean_IR_toIR___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
