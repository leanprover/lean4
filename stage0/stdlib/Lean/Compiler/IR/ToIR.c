// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: public import Lean.Compiler.IR.CompilerM public import Lean.Compiler.IR.ToIRType
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
extern lean_object* l_Lean_IR_instInhabitedArg_default;
static lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__11;
lean_object* l_Lean_IR_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Lean_IR_IRType_isVoid(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__1;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__8;
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
lean_object* l_Lean_IR_CtorInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__16;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__1;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__3;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2;
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__15;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__7;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(size_t, size_t, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__13;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__9;
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody_default__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__1;
extern lean_object* l_Lean_IR_declMapExt;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__3;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity_spec__0(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__0;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__14;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_BuilderState_ctorIdx(lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM;
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__4;
lean_object* l_Lean_IR_IRType_boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__6;
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4;
lean_object* l_Lean_IR_getCtorLayout(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__12;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3;
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object**);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_IR_nameToIRType(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__4;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_BuilderState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__9;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx(lean_object*);
extern lean_object* l_Lean_IR_instInhabitedExpr_default;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx___boxed(lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__5;
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIR___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__10;
lean_object* l_Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___closed__0;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2;
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_BuilderState_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_BuilderState_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ToIR_BuilderState_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftT___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6;
x_2 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5;
x_2 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
x_2 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0___boxed), 5, 0);
x_12 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_13 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_15, 0, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_18, 0, x_8);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_19, 0, x_7);
lean_ctor_set(x_3, 4, x_17);
lean_ctor_set(x_3, 3, x_18);
lean_ctor_set(x_3, 2, x_19);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_16);
lean_ctor_set(x_1, 1, x_13);
x_20 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11;
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, lean_box(0));
lean_closure_set(x_21, 4, lean_box(0));
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_26 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0___boxed), 5, 0);
x_27 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_28 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_22);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_29, 0, x_22);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_32, 0, x_25);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_33, 0, x_24);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_34, 0, x_23);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_35);
x_36 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11;
x_37 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, lean_box(0));
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, lean_box(0));
lean_closure_set(x_37, 4, lean_box(0));
lean_closure_set(x_37, 5, x_36);
lean_closure_set(x_37, 6, x_26);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 4);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0___boxed), 5, 0);
x_45 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_46 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_39);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_47, 0, x_39);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_50, 0, x_42);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_51, 0, x_41);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_52, 0, x_40);
if (lean_is_scalar(x_43)) {
 x_53 = lean_alloc_ctor(0, 5, 0);
} else {
 x_53 = x_43;
}
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
x_55 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11;
x_56 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_56, 0, lean_box(0));
lean_closure_set(x_56, 1, lean_box(0));
lean_closure_set(x_56, 2, x_54);
lean_closure_set(x_56, 3, lean_box(0));
lean_closure_set(x_56, 4, lean_box(0));
lean_closure_set(x_56, 5, x_55);
lean_closure_set(x_56, 6, x_44);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 3);
x_9 = lean_apply_1(x_1, x_8);
lean_ctor_set(x_6, 3, x_9);
x_10 = lean_st_ref_set(x_2, x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstStateM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
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
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_ToIR_M_run___redArg___closed__5;
x_6 = lean_st_mk_ref(x_5);
lean_inc(x_6);
x_7 = lean_apply_4(x_1, x_6, x_2, x_3, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec_ref(x_9);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec_ref(x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_M_run___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(142u);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1;
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3;
x_5 = lean_panic_fn(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_instBEqFVarId_beq(x_6, x_2);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_instHashableFVarId_hash(x_3);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_4, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_1, x_3, x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ToIR_getFVarValue___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedArg_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = 0;
x_7 = l_Lean_Compiler_LCNF_normFVarImp(x_5, x_1, x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_st_ref_get(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_12, x_11, x_9);
lean_dec(x_9);
lean_dec_ref(x_11);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_st_ref_get(x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_18 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_17, x_16, x_14);
lean_dec(x_14);
lean_dec_ref(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getFVarValue(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_6, x_5, x_1);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getJoinPointValue(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_instHashableFVarId_hash(x_4);
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
x_26 = l_Lean_instHashableFVarId_hash(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object* x_1) {
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
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_instHashableFVarId_hash(x_2);
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
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
lean_ctor_set(x_4, 2, x_11);
lean_ctor_set(x_4, 0, x_9);
x_12 = lean_st_ref_set(x_2, x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_ctor_get(x_4, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_14, x_1, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_16, x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_17);
x_23 = lean_st_ref_set(x_2, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_16);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0(x_1, x_2, x_3);
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
x_4 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_7, x_1, x_8);
lean_ctor_set(x_5, 0, x_9);
x_10 = lean_st_ref_set(x_3, x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_ctor_get(x_5, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_13, x_1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
x_20 = lean_st_ref_set(x_3, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_ctor_set(x_3, 2, x_7);
x_8 = lean_st_ref_set(x_1, x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_13);
x_17 = lean_st_ref_set(x_1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar___redArg(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_newVar___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_ctor_set(x_4, 2, x_10);
lean_ctor_set(x_4, 1, x_8);
x_11 = lean_st_ref_set(x_2, x_4);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
lean_inc(x_15);
x_17 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_14, x_1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_15, x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_16);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(1);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = lean_st_ref_set(x_2, x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_16 = lean_box(1);
x_17 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_12, x_1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ir_find_env_decl(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 5);
lean_dec(x_7);
x_8 = l_Lean_IR_ToIR_addDecl___redArg___closed__0;
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_8, x_6, x_1, x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_IR_ToIR_addDecl___redArg___closed__3;
lean_ctor_set(x_4, 5, x_13);
lean_ctor_set(x_4, 0, x_12);
x_14 = lean_st_ref_set(x_2, x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 6);
x_23 = lean_ctor_get(x_4, 7);
x_24 = lean_ctor_get(x_4, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_25 = l_Lean_IR_ToIR_addDecl___redArg___closed__0;
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_box(0);
x_29 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_25, x_17, x_1, x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_IR_ToIR_addDecl___redArg___closed__3;
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
x_32 = lean_st_ref_set(x_2, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_IR_ToIR_getFVarValue___redArg(x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerArg___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ToIR_TranslatedProj_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_TranslatedProj_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedExpr_default;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj_default;
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
static lean_object* _init_l_Lean_IR_ToIR_lowerProj___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(13);
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
case 3:
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
default: 
{
lean_object* x_40; 
lean_dec(x_1);
x_40 = l_Lean_IR_ToIR_lowerProj___closed__1;
return x_40;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_instBEqFVarId_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_instBEqFVarId_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_instHashableFVarId_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_instHashableFVarId_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
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
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
lean_inc(x_6);
x_9 = l_Lean_IR_ToIR_bindVar___redArg(x_6, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_toIRType(x_7, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_18; uint8_t x_34; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_13 = x_11;
} else {
 lean_dec_ref(x_11);
 x_13 = lean_box(0);
}
x_34 = l_Lean_IR_IRType_isVoid(x_12);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_IR_IRType_isErased(x_12);
x_18 = x_35;
goto block_33;
}
else
{
x_18 = x_34;
goto block_33;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_8);
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_33:
{
if (x_18 == 0)
{
lean_dec(x_6);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_st_ref_take(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 3);
x_22 = lean_box(0);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_21, x_6, x_22);
lean_ctor_set(x_19, 3, x_23);
x_24 = lean_st_ref_set(x_2, x_19);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_ctor_get(x_19, 2);
x_28 = lean_ctor_get(x_19, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_28, x_6, x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_st_ref_set(x_2, x_31);
x_14 = lean_box(0);
goto block_17;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerParam(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedFnBody_default__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 2);
x_13 = lean_ctor_get(x_8, 3);
x_14 = lean_ctor_get(x_8, 4);
x_15 = lean_ctor_get(x_8, 1);
lean_dec(x_15);
x_16 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_17 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_11);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_11);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_13);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_23, 0, x_12);
lean_ctor_set(x_8, 4, x_21);
lean_ctor_set(x_8, 3, x_22);
lean_ctor_set(x_8, 2, x_23);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_20);
lean_ctor_set(x_6, 1, x_17);
x_24 = l_ReaderT_instMonad___redArg(x_6);
x_25 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0;
x_26 = l_instInhabitedOfMonad___redArg(x_24, x_25);
x_27 = lean_panic_fn(x_26, x_1);
x_28 = lean_apply_4(x_27, x_2, x_3, x_4, lean_box(0));
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
x_32 = lean_ctor_get(x_8, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_33 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_34 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_29);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_29);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_31);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_40, 0, x_30);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_39);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_6, 1, x_34);
lean_ctor_set(x_6, 0, x_41);
x_42 = l_ReaderT_instMonad___redArg(x_6);
x_43 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0;
x_44 = l_instInhabitedOfMonad___redArg(x_42, x_43);
x_45 = lean_panic_fn(x_44, x_1);
x_46 = lean_apply_4(x_45, x_2, x_3, x_4, lean_box(0));
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
lean_dec(x_6);
x_48 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 4);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
x_53 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_54 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
lean_inc_ref(x_48);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_55, 0, x_48);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_51);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_59, 0, x_50);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_60, 0, x_49);
if (lean_is_scalar(x_52)) {
 x_61 = lean_alloc_ctor(0, 5, 0);
} else {
 x_61 = x_52;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
x_63 = l_ReaderT_instMonad___redArg(x_62);
x_64 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0;
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_4(x_66, x_2, x_3, x_4, lean_box(0));
return x_67;
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
x_3 = lean_unsigned_to_nat(316u);
x_4 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_45; lean_object* x_52; uint8_t x_53; 
x_52 = lean_array_get_size(x_4);
x_53 = lean_nat_dec_lt(x_6, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_45 = x_54;
goto block_51;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_array_fget_borrowed(x_4, x_6);
lean_inc_ref(x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_45 = x_56;
goto block_51;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3;
x_16 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_15, x_11, x_12, x_13);
return x_16;
}
block_44:
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_IR_ToIR_lowerCode(x_2, x_7, x_8, x_9);
return x_20;
}
else
{
lean_dec_ref(x_19);
lean_dec_ref(x_2);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = lean_box(0);
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
x_14 = lean_box(0);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_IR_ToIR_bindVar___redArg(x_27, x_7);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_6);
x_32 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_31, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_dec(x_29);
lean_dec_ref(x_26);
lean_dec(x_25);
return x_32;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_23);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = l_Lean_IR_ToIR_bindErased___redArg(x_39, x_7);
lean_dec_ref(x_40);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_6, x_41);
lean_dec(x_6);
x_6 = x_42;
goto _start;
}
}
}
}
block_51:
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_array_get_size(x_5);
x_47 = lean_nat_dec_lt(x_6, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_box(0);
x_18 = x_45;
x_19 = x_48;
goto block_44;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_array_fget_borrowed(x_5, x_6);
lean_inc(x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_18 = x_45;
x_19 = x_50;
goto block_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_3, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
x_11 = l_Lean_IR_ToIR_lowerParam(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_14, x_2, x_12);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_IR_ToIR_lowerArg___redArg(x_8, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_12, x_2, x_10);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
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
x_12 = l_Lean_IR_ToIR_lowerAlt(x_1, x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_15, x_3, x_13);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___closed__0;
x_18 = lean_array_get_borrowed(x_17, x_1, x_6);
x_19 = lean_nat_dec_eq(x_6, x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = l_Lean_IR_ToIR_bindErased___redArg(x_20, x_7);
lean_dec_ref(x_21);
x_9 = x_3;
x_10 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_st_ref_take(x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_22, 3);
lean_inc(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
lean_inc(x_24);
x_28 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_26, x_24, x_27);
lean_ctor_set(x_22, 3, x_28);
x_29 = lean_st_ref_set(x_7, x_22);
x_9 = x_3;
x_10 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_4, 2);
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
x_34 = lean_ctor_get(x_22, 2);
x_35 = lean_ctor_get(x_22, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
lean_inc(x_31);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
lean_inc(x_30);
x_37 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_35, x_30, x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_st_ref_set(x_7, x_38);
x_9 = x_3;
x_10 = lean_box(0);
goto block_16;
}
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_13 = lean_nat_dec_lt(x_12, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
x_6 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_1, x_2, x_3, x_4, x_8, x_11, x_14);
return x_18;
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
x_3 = lean_unsigned_to_nat(158u);
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
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__3;
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(150u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: cases.alts.size == 1\n      ", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(137u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ctorName == info.ctorName\n      ", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__8;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(139u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: info.fieldIdx < ps.size\n      ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__10;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(140u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__3;
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_unsigned_to_nat(138u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_IR_ToIR_lowerLet(x_6, x_7, x_2, x_3, x_4);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_1);
x_9 = l_Lean_IR_ToIR_lowerCode___closed__2;
x_10 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_9, x_2, x_3, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
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
x_16 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_13, x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_array_size(x_14);
x_19 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_18, x_19, x_14, x_2, x_3, x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_22 = l_Lean_IR_ToIR_lowerCode(x_15, x_2, x_3, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_IR_ToIR_lowerCode(x_12, x_2, x_3, x_4);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_17);
return x_24;
}
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_22;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
case 3:
{
uint8_t x_34; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_35, x_2);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_array_size(x_36);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_39, x_40, x_36, x_2);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_ctor_set_tag(x_1, 11);
lean_ctor_set(x_1, 1, x_43);
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set(x_41, 0, x_1);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set_tag(x_1, 11);
lean_ctor_set(x_1, 1, x_44);
lean_ctor_set(x_1, 0, x_38);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_1);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_48 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_46, x_2);
lean_dec(x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_array_size(x_47);
x_51 = 0;
x_52 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_50, x_51, x_47, x_2);
lean_dec(x_2);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_53);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
case 4:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_57);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_57, 0);
x_59 = lean_ctor_get(x_57, 2);
x_60 = lean_ctor_get(x_57, 3);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_58);
x_61 = l_Lean_IR_hasTrivialStructure_x3f(x_58, x_3, x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
lean_inc_ref(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_57, 3);
lean_dec(x_64);
x_65 = lean_ctor_get(x_57, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_57, 0);
lean_dec(x_67);
x_68 = l_Lean_IR_ToIR_getFVarValue___redArg(x_59, x_2);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_58);
x_71 = l_Lean_IR_nameToIRType(x_58, x_3, x_4);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = lean_array_size(x_60);
x_74 = 0;
lean_inc(x_70);
x_75 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_70, x_73, x_74, x_60, x_2, x_3, x_4);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_ctor_set_tag(x_57, 9);
lean_ctor_set(x_57, 3, x_77);
lean_ctor_set(x_57, 2, x_72);
lean_ctor_set(x_57, 1, x_70);
lean_ctor_set(x_75, 0, x_57);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
lean_ctor_set_tag(x_57, 9);
lean_ctor_set(x_57, 3, x_78);
lean_ctor_set(x_57, 2, x_72);
lean_ctor_set(x_57, 1, x_70);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_57);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_70);
lean_free_object(x_57);
lean_dec(x_58);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
return x_75;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_70);
lean_free_object(x_57);
lean_dec_ref(x_60);
lean_dec(x_58);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_71);
if (x_83 == 0)
{
return x_71;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_71, 0);
lean_inc(x_84);
lean_dec(x_71);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_free_object(x_57);
lean_dec_ref(x_60);
lean_dec(x_58);
x_86 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_87 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_86, x_2, x_3, x_4);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_57);
x_88 = l_Lean_IR_ToIR_getFVarValue___redArg(x_59, x_2);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_58);
x_91 = l_Lean_IR_nameToIRType(x_58, x_3, x_4);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = lean_array_size(x_60);
x_94 = 0;
lean_inc(x_90);
x_95 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_90, x_93, x_94, x_60, x_2, x_3, x_4);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_98, 0, x_58);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_92);
lean_ctor_set(x_98, 3, x_96);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 1, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_58);
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_101 = x_95;
} else {
 lean_dec_ref(x_95);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec_ref(x_60);
lean_dec(x_58);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_104 = x_91;
} else {
 lean_dec_ref(x_91);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_60);
lean_dec(x_58);
x_106 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_107 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_106, x_2, x_3, x_4);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_62, 0);
lean_inc(x_108);
lean_dec_ref(x_62);
x_109 = lean_array_get_size(x_60);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_dec_eq(x_109, x_110);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_108);
lean_dec_ref(x_57);
x_112 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_113 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_112, x_2, x_3, x_4);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = l_Lean_IR_ToIR_lowerCode___closed__7;
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_array_get_borrowed(x_114, x_60, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_117 = lean_ctor_get(x_116, 0);
x_118 = lean_ctor_get(x_116, 1);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_116, 2);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_108, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_108, 2);
lean_inc(x_121);
lean_dec(x_108);
x_122 = lean_name_eq(x_117, x_120);
lean_dec(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_121);
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_57);
x_123 = l_Lean_IR_ToIR_lowerCode___closed__9;
x_124 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_123, x_2, x_3, x_4);
return x_124;
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_array_get_size(x_118);
x_126 = lean_nat_dec_lt(x_121, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_121);
lean_dec_ref(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_57);
x_127 = l_Lean_IR_ToIR_lowerCode___closed__11;
x_128 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_127, x_2, x_3, x_4);
return x_128;
}
else
{
uint8_t x_129; 
x_129 = lean_nat_dec_lt(x_115, x_125);
if (x_129 == 0)
{
lean_dec(x_125);
lean_dec(x_121);
lean_dec_ref(x_118);
lean_dec_ref(x_57);
x_1 = x_119;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_box(0);
x_132 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_118, x_121, x_131, x_57, x_125, x_115, x_2);
lean_dec(x_125);
lean_dec_ref(x_57);
lean_dec(x_121);
lean_dec_ref(x_118);
lean_dec_ref(x_132);
x_1 = x_119;
goto _start;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_108);
lean_dec_ref(x_57);
x_134 = l_Lean_IR_ToIR_lowerCode___closed__12;
x_135 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_134, x_2, x_3, x_4);
return x_135;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec_ref(x_57);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_61);
if (x_136 == 0)
{
return x_61;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_61, 0);
lean_inc(x_137);
lean_dec(x_61);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
case 5:
{
uint8_t x_139; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_139 = !lean_is_exclusive(x_1);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_1, 0);
x_141 = l_Lean_IR_ToIR_getFVarValue___redArg(x_140, x_2);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_141, 0);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_143);
lean_ctor_set(x_141, 0, x_1);
return x_141;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
lean_dec(x_141);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_144);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_1);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
lean_dec(x_1);
x_147 = l_Lean_IR_ToIR_getFVarValue___redArg(x_146, x_2);
lean_dec(x_2);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
x_150 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_150, 0, x_148);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 1, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
default: 
{
uint8_t x_152; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_1);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_1, 0);
lean_dec(x_153);
x_154 = lean_box(12);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_154);
return x_1;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_1);
x_155 = lean_box(12);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_IR_getCtorLayout(x_7, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_13, x_8, x_14, x_15, x_3, x_4, x_5);
lean_dec_ref(x_14);
lean_dec_ref(x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_11, 1, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_11);
lean_dec_ref(x_13);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_24, x_8, x_25, x_26, x_3, x_4, x_5);
lean_dec_ref(x_25);
lean_dec_ref(x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_24);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_33 = x_27;
} else {
 lean_dec_ref(x_27);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_10, 0);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = l_Lean_IR_ToIR_lowerCode(x_39, x_3, x_4, x_5);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set(x_40, 0, x_2);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_2, 0, x_43);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_2);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_2);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_IR_ToIR_lowerCode(x_48, x_3, x_4, x_5);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
x_9 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_MessageData_tagWithErrorName(x_2, x_1);
x_8 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(x_7, x_3, x_4);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_16; 
x_16 = lean_array_fget_borrowed(x_1, x_6);
switch (lean_obj_tag(x_16)) {
case 1:
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_2);
x_17 = lean_array_get_borrowed(x_2, x_3, x_6);
lean_inc(x_17);
x_18 = lean_array_push(x_5, x_17);
x_8 = x_18;
x_9 = lean_box(0);
goto block_15;
}
case 2:
{
x_8 = x_5;
x_9 = lean_box(0);
goto block_15;
}
case 3:
{
x_8 = x_5;
x_9 = lean_box(0);
goto block_15;
}
default: 
{
x_8 = x_5;
x_9 = lean_box(0);
goto block_15;
}
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
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
x_5 = x_8;
x_6 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_1, x_2, x_3, x_7, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(x_1, x_2, x_3);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_2, x_4, x_5);
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
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_unsigned_to_nat(178u);
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
x_3 = lean_unsigned_to_nat(248u);
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
x_1 = lean_mk_string_unchecked("`", 1, 1);
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
x_1 = lean_mk_string_unchecked("` not supported by code generator; consider marking definition as `noncomputable`", 81, 81);
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
x_1 = lean_mk_string_unchecked("code generator does not support recursor `", 42, 42);
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
x_1 = lean_mk_string_unchecked("` yet, consider using 'match ... with' and/or structural recursion", 66, 66);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_17);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 x_18 = x_14;
} else {
 lean_dec_ref(x_14);
 x_18 = lean_box(0);
}
x_19 = 0;
lean_inc(x_16);
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_17, x_16, x_19);
lean_dec_ref(x_17);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_15);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_IR_ToIR_lowerLitValue(x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set_tag(x_22, 11);
lean_ctor_set(x_22, 0, x_26);
if (lean_is_scalar(x_18)) {
 x_31 = lean_alloc_ctor(0, 4, 0);
} else {
 x_31 = x_18;
}
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set_tag(x_22, 11);
lean_ctor_set(x_22, 0, x_26);
if (lean_is_scalar(x_18)) {
 x_33 = lean_alloc_ctor(0, 4, 0);
} else {
 x_33 = x_18;
}
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_18);
return x_28;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = l_Lean_IR_ToIR_lowerLitValue(x_21);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_42, 0, x_37);
if (lean_is_scalar(x_18)) {
 x_43 = lean_alloc_ctor(0, 4, 0);
} else {
 x_43 = x_18;
}
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_40);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_18);
return x_39;
}
}
}
case 1:
{
lean_object* x_45; 
lean_dec(x_18);
x_45 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5);
return x_45;
}
case 2:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_15);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_20, 2);
lean_inc(x_48);
lean_dec_ref(x_20);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_46);
x_49 = l_Lean_IR_hasTrivialStructure_x3f(x_46, x_4, x_5);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_IR_ToIR_getFVarValue___redArg(x_48, x_3);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_st_ref_get(x_5);
x_55 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_Environment_find_x3f(x_55, x_46, x_19);
if (lean_obj_tag(x_56) == 0)
{
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
if (lean_obj_tag(x_57) == 5)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_58);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_58, 4);
lean_inc(x_59);
lean_dec_ref(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 1);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec_ref(x_59);
lean_inc(x_5);
lean_inc_ref(x_4);
x_62 = l_Lean_IR_getCtorLayout(x_61, x_4, x_5);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_65);
lean_dec(x_63);
x_66 = lean_box(0);
x_67 = lean_array_get(x_66, x_65, x_47);
lean_dec(x_47);
lean_dec_ref(x_65);
x_68 = l_Lean_IR_ToIR_lowerProj(x_53, x_64, x_67);
lean_dec_ref(x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_71);
lean_dec_ref(x_69);
x_72 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
if (lean_is_scalar(x_18)) {
 x_77 = lean_alloc_ctor(0, 4, 0);
} else {
 x_77 = x_18;
}
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_71);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
lean_dec(x_74);
if (lean_is_scalar(x_18)) {
 x_79 = lean_alloc_ctor(0, 4, 0);
} else {
 x_79 = x_18;
}
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_71);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec(x_18);
return x_74;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_68);
lean_dec(x_18);
x_81 = l_Lean_IR_ToIR_bindErased___redArg(x_15, x_3);
lean_dec_ref(x_81);
x_82 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_83 = !lean_is_exclusive(x_62);
if (x_83 == 0)
{
return x_62;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_62, 0);
lean_inc(x_84);
lean_dec(x_62);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_dec_ref(x_59);
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = lean_box(0);
goto block_13;
}
}
}
else
{
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = lean_box(0);
goto block_13;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_18);
x_86 = l_Lean_IR_ToIR_bindErased___redArg(x_15, x_3);
lean_dec_ref(x_86);
x_87 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_46);
lean_dec(x_18);
x_88 = !lean_is_exclusive(x_50);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_50, 0);
x_90 = lean_ctor_get(x_89, 2);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_nat_dec_eq(x_90, x_47);
lean_dec(x_47);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_free_object(x_50);
lean_dec(x_48);
x_92 = l_Lean_IR_ToIR_bindErased___redArg(x_15, x_3);
lean_dec_ref(x_92);
x_93 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_93;
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_st_ref_take(x_3);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_94, 3);
lean_ctor_set(x_50, 0, x_48);
x_97 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_96, x_15, x_50);
lean_ctor_set(x_94, 3, x_97);
x_98 = lean_st_ref_set(x_3, x_94);
x_99 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_94, 0);
x_101 = lean_ctor_get(x_94, 1);
x_102 = lean_ctor_get(x_94, 2);
x_103 = lean_ctor_get(x_94, 3);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_94);
lean_ctor_set(x_50, 0, x_48);
x_104 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_103, x_15, x_50);
x_105 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_101);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_104);
x_106 = lean_st_ref_set(x_3, x_105);
x_107 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_50, 0);
lean_inc(x_108);
lean_dec(x_50);
x_109 = lean_ctor_get(x_108, 2);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_nat_dec_eq(x_109, x_47);
lean_dec(x_47);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_48);
x_111 = l_Lean_IR_ToIR_bindErased___redArg(x_15, x_3);
lean_dec_ref(x_111);
x_112 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_113 = lean_st_ref_take(x_3);
x_114 = lean_ctor_get(x_113, 0);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_113, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 3);
lean_inc_ref(x_117);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 x_118 = x_113;
} else {
 lean_dec_ref(x_113);
 x_118 = lean_box(0);
}
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_48);
x_120 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_117, x_15, x_119);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 4, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_115);
lean_ctor_set(x_121, 2, x_116);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_3, x_121);
x_123 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_124 = !lean_is_exclusive(x_49);
if (x_124 == 0)
{
return x_49;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_49, 0);
lean_inc(x_125);
lean_dec(x_49);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
case 3:
{
lean_object* x_127; lean_object* x_128; size_t x_129; size_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_127 = lean_ctor_get(x_20, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_128);
lean_dec_ref(x_20);
x_129 = lean_array_size(x_128);
x_130 = 0;
lean_inc_ref(x_128);
x_131 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_129, x_130, x_128, x_3);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
lean_inc(x_127);
x_133 = l_Lean_IR_ToIR_findDecl___redArg(x_127, x_5);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
lean_inc(x_127);
x_135 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_127, x_5);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_st_ref_get(x_5);
x_138 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_138);
lean_dec_ref(x_137);
lean_inc(x_127);
x_139 = l_Lean_Environment_find_x3f(x_138, x_127, x_19);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec(x_18);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_140 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_141 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_140, x_3, x_4, x_5);
return x_141;
}
else
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
lean_dec_ref(x_139);
switch (lean_obj_tag(x_142)) {
case 0:
{
uint8_t x_143; 
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_18);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_142, 0);
lean_dec(x_144);
x_145 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_146 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_147 = 1;
x_148 = l_Lean_Name_toString(x_127, x_147);
lean_ctor_set_tag(x_142, 3);
lean_ctor_set(x_142, 0, x_148);
x_149 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_142);
x_150 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_151 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_MessageData_ofFormat(x_151);
x_153 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_145, x_152, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_142);
x_154 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_155 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_156 = 1;
x_157 = l_Lean_Name_toString(x_127, x_156);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_MessageData_ofFormat(x_161);
x_163 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_154, x_162, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_163;
}
}
case 2:
{
uint8_t x_164; 
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_18);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_164 = !lean_is_exclusive(x_142);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_142, 0);
lean_dec(x_165);
x_166 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_167 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_168 = 1;
x_169 = l_Lean_Name_toString(x_127, x_168);
lean_ctor_set_tag(x_142, 3);
lean_ctor_set(x_142, 0, x_169);
x_170 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_142);
x_171 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_172 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_MessageData_ofFormat(x_172);
x_174 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_166, x_173, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_142);
x_175 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_176 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_177 = 1;
x_178 = l_Lean_Name_toString(x_127, x_177);
x_179 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_182 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_MessageData_ofFormat(x_182);
x_184 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_175, x_183, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_184;
}
}
case 4:
{
uint8_t x_185; 
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_18);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_185 = !lean_is_exclusive(x_142);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_186 = lean_ctor_get(x_142, 0);
lean_dec(x_186);
x_187 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_188 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_189 = 1;
x_190 = l_Lean_Name_toString(x_127, x_189);
lean_ctor_set_tag(x_142, 3);
lean_ctor_set(x_142, 0, x_190);
x_191 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_142);
x_192 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_193 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_MessageData_ofFormat(x_193);
x_195 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_187, x_194, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_142);
x_196 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_197 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_198 = 1;
x_199 = l_Lean_Name_toString(x_127, x_198);
x_200 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_203 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_MessageData_ofFormat(x_203);
x_205 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_196, x_204, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_205;
}
}
case 5:
{
uint8_t x_206; 
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_18);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_206 = !lean_is_exclusive(x_142);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_142, 0);
lean_dec(x_207);
x_208 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_209 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_210 = 1;
x_211 = l_Lean_Name_toString(x_127, x_210);
lean_ctor_set_tag(x_142, 3);
lean_ctor_set(x_142, 0, x_211);
x_212 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_142);
x_213 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_214 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_MessageData_ofFormat(x_214);
x_216 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_208, x_215, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_142);
x_217 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_218 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_219 = 1;
x_220 = l_Lean_Name_toString(x_127, x_219);
x_221 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_224 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_MessageData_ofFormat(x_224);
x_226 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_217, x_225, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_226;
}
}
case 6:
{
uint8_t x_227; 
lean_inc(x_15);
lean_dec_ref(x_1);
x_227 = !lean_is_exclusive(x_142);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_142, 0);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_228, 3);
lean_inc(x_231);
lean_dec_ref(x_228);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_229);
x_232 = l_Lean_IR_hasTrivialStructure_x3f(x_229, x_4, x_5);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
lean_dec_ref(x_128);
lean_inc(x_5);
lean_inc_ref(x_4);
x_234 = l_Lean_IR_nameToIRType(x_229, x_4, x_5);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec_ref(x_234);
x_236 = l_Lean_IR_IRType_isScalar(x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_235);
lean_dec(x_230);
lean_free_object(x_142);
lean_inc(x_5);
lean_inc_ref(x_4);
x_237 = l_Lean_IR_getCtorLayout(x_127, x_4, x_5);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_243 = lean_ctor_get(x_238, 0);
lean_inc_ref(x_243);
x_244 = lean_ctor_get(x_238, 1);
lean_inc_ref(x_244);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_245 = x_238;
} else {
 lean_dec_ref(x_238);
 x_245 = lean_box(0);
}
x_246 = lean_array_get_size(x_132);
x_247 = l_Array_extract___redArg(x_132, x_231, x_246);
lean_dec(x_132);
x_264 = lean_array_get_size(x_247);
x_265 = lean_array_get_size(x_244);
x_266 = lean_nat_dec_eq(x_264, x_265);
lean_dec(x_264);
if (x_266 == 0)
{
lean_dec(x_265);
lean_dec_ref(x_247);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_242;
}
else
{
if (x_236 == 0)
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec(x_239);
x_267 = lean_unsigned_to_nat(0u);
x_268 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_269 = lean_nat_dec_lt(x_267, x_265);
if (x_269 == 0)
{
lean_dec(x_265);
x_248 = x_268;
x_249 = lean_box(0);
goto block_263;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_271 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_244, x_270, x_247, x_265, x_268, x_267);
lean_dec(x_265);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_248 = x_272;
x_249 = lean_box(0);
goto block_263;
}
}
else
{
lean_dec(x_265);
lean_dec_ref(x_247);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_242;
}
}
block_242:
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_box(12);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(0, 1, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_240);
return x_241;
}
block_263:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
lean_inc(x_251);
x_252 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_243, x_244, x_247, x_251, x_3, x_4, x_5);
lean_dec_ref(x_247);
lean_dec_ref(x_244);
if (lean_obj_tag(x_252) == 0)
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_252, 0);
x_255 = l_Lean_IR_CtorInfo_type(x_243);
if (lean_is_scalar(x_245)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_245;
}
lean_ctor_set(x_256, 0, x_243);
lean_ctor_set(x_256, 1, x_248);
if (lean_is_scalar(x_18)) {
 x_257 = lean_alloc_ctor(0, 4, 0);
} else {
 x_257 = x_18;
}
lean_ctor_set(x_257, 0, x_251);
lean_ctor_set(x_257, 1, x_255);
lean_ctor_set(x_257, 2, x_256);
lean_ctor_set(x_257, 3, x_254);
lean_ctor_set(x_252, 0, x_257);
return x_252;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_252, 0);
lean_inc(x_258);
lean_dec(x_252);
x_259 = l_Lean_IR_CtorInfo_type(x_243);
if (lean_is_scalar(x_245)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_245;
}
lean_ctor_set(x_260, 0, x_243);
lean_ctor_set(x_260, 1, x_248);
if (lean_is_scalar(x_18)) {
 x_261 = lean_alloc_ctor(0, 4, 0);
} else {
 x_261 = x_18;
}
lean_ctor_set(x_261, 0, x_251);
lean_ctor_set(x_261, 1, x_259);
lean_ctor_set(x_261, 2, x_260);
lean_ctor_set(x_261, 3, x_258);
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_261);
return x_262;
}
}
else
{
lean_dec(x_251);
lean_dec_ref(x_248);
lean_dec(x_245);
lean_dec_ref(x_243);
lean_dec(x_18);
return x_252;
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_231);
lean_dec(x_132);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_273 = !lean_is_exclusive(x_237);
if (x_273 == 0)
{
return x_237;
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_237, 0);
lean_inc(x_274);
lean_dec(x_237);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
return x_275;
}
}
}
else
{
lean_object* x_276; uint8_t x_277; 
lean_dec(x_231);
lean_dec(x_132);
lean_dec(x_127);
x_276 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_279) == 0)
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_279, 0);
lean_ctor_set(x_276, 0, x_230);
lean_ctor_set_tag(x_142, 11);
lean_ctor_set(x_142, 0, x_276);
if (lean_is_scalar(x_18)) {
 x_282 = lean_alloc_ctor(0, 4, 0);
} else {
 x_282 = x_18;
}
lean_ctor_set(x_282, 0, x_278);
lean_ctor_set(x_282, 1, x_235);
lean_ctor_set(x_282, 2, x_142);
lean_ctor_set(x_282, 3, x_281);
lean_ctor_set(x_279, 0, x_282);
return x_279;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_279, 0);
lean_inc(x_283);
lean_dec(x_279);
lean_ctor_set(x_276, 0, x_230);
lean_ctor_set_tag(x_142, 11);
lean_ctor_set(x_142, 0, x_276);
if (lean_is_scalar(x_18)) {
 x_284 = lean_alloc_ctor(0, 4, 0);
} else {
 x_284 = x_18;
}
lean_ctor_set(x_284, 0, x_278);
lean_ctor_set(x_284, 1, x_235);
lean_ctor_set(x_284, 2, x_142);
lean_ctor_set(x_284, 3, x_283);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
else
{
lean_free_object(x_276);
lean_dec(x_278);
lean_dec(x_235);
lean_dec(x_230);
lean_free_object(x_142);
lean_dec(x_18);
return x_279;
}
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_276, 0);
lean_inc(x_286);
lean_dec(x_276);
x_287 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_289 = x_287;
} else {
 lean_dec_ref(x_287);
 x_289 = lean_box(0);
}
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_230);
lean_ctor_set_tag(x_142, 11);
lean_ctor_set(x_142, 0, x_290);
if (lean_is_scalar(x_18)) {
 x_291 = lean_alloc_ctor(0, 4, 0);
} else {
 x_291 = x_18;
}
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_235);
lean_ctor_set(x_291, 2, x_142);
lean_ctor_set(x_291, 3, x_288);
if (lean_is_scalar(x_289)) {
 x_292 = lean_alloc_ctor(0, 1, 0);
} else {
 x_292 = x_289;
}
lean_ctor_set(x_292, 0, x_291);
return x_292;
}
else
{
lean_dec(x_286);
lean_dec(x_235);
lean_dec(x_230);
lean_free_object(x_142);
lean_dec(x_18);
return x_287;
}
}
}
}
else
{
uint8_t x_293; 
lean_dec(x_231);
lean_dec(x_230);
lean_free_object(x_142);
lean_dec(x_132);
lean_dec(x_127);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_293 = !lean_is_exclusive(x_234);
if (x_293 == 0)
{
return x_234;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_234, 0);
lean_inc(x_294);
lean_dec(x_234);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_294);
return x_295;
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_free_object(x_142);
lean_dec(x_132);
lean_dec(x_127);
lean_dec(x_18);
x_296 = lean_ctor_get(x_233, 0);
lean_inc(x_296);
lean_dec_ref(x_233);
x_297 = lean_st_ref_take(x_3);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_296, 2);
lean_inc(x_299);
lean_dec(x_296);
x_300 = !lean_is_exclusive(x_297);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_301 = lean_ctor_get(x_297, 3);
x_302 = lean_box(0);
x_303 = lean_nat_add(x_298, x_299);
lean_dec(x_299);
lean_dec(x_298);
x_304 = lean_array_get(x_302, x_128, x_303);
lean_dec(x_303);
lean_dec_ref(x_128);
x_305 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_301, x_15, x_304);
lean_ctor_set(x_297, 3, x_305);
x_306 = lean_st_ref_set(x_3, x_297);
x_307 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_308 = lean_ctor_get(x_297, 0);
x_309 = lean_ctor_get(x_297, 1);
x_310 = lean_ctor_get(x_297, 2);
x_311 = lean_ctor_get(x_297, 3);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_297);
x_312 = lean_box(0);
x_313 = lean_nat_add(x_298, x_299);
lean_dec(x_299);
lean_dec(x_298);
x_314 = lean_array_get(x_312, x_128, x_313);
lean_dec(x_313);
lean_dec_ref(x_128);
x_315 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_311, x_15, x_314);
x_316 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_316, 0, x_308);
lean_ctor_set(x_316, 1, x_309);
lean_ctor_set(x_316, 2, x_310);
lean_ctor_set(x_316, 3, x_315);
x_317 = lean_st_ref_set(x_3, x_316);
x_318 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_318;
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_free_object(x_142);
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_319 = !lean_is_exclusive(x_232);
if (x_319 == 0)
{
return x_232;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_232, 0);
lean_inc(x_320);
lean_dec(x_232);
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_320);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_322 = lean_ctor_get(x_142, 0);
lean_inc(x_322);
lean_dec(x_142);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 3);
lean_inc(x_325);
lean_dec_ref(x_322);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_323);
x_326 = l_Lean_IR_hasTrivialStructure_x3f(x_323, x_4, x_5);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
lean_dec_ref(x_326);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; 
lean_dec_ref(x_128);
lean_inc(x_5);
lean_inc_ref(x_4);
x_328 = l_Lean_IR_nameToIRType(x_323, x_4, x_5);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; uint8_t x_330; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec_ref(x_328);
x_330 = l_Lean_IR_IRType_isScalar(x_329);
if (x_330 == 0)
{
lean_object* x_331; 
lean_dec(x_329);
lean_dec(x_324);
lean_inc(x_5);
lean_inc_ref(x_4);
x_331 = l_Lean_IR_getCtorLayout(x_127, x_4, x_5);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
x_337 = lean_ctor_get(x_332, 0);
lean_inc_ref(x_337);
x_338 = lean_ctor_get(x_332, 1);
lean_inc_ref(x_338);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_339 = x_332;
} else {
 lean_dec_ref(x_332);
 x_339 = lean_box(0);
}
x_340 = lean_array_get_size(x_132);
x_341 = l_Array_extract___redArg(x_132, x_325, x_340);
lean_dec(x_132);
x_354 = lean_array_get_size(x_341);
x_355 = lean_array_get_size(x_338);
x_356 = lean_nat_dec_eq(x_354, x_355);
lean_dec(x_354);
if (x_356 == 0)
{
lean_dec(x_355);
lean_dec_ref(x_341);
lean_dec(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_337);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_336;
}
else
{
if (x_330 == 0)
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; 
lean_dec(x_333);
x_357 = lean_unsigned_to_nat(0u);
x_358 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_359 = lean_nat_dec_lt(x_357, x_355);
if (x_359 == 0)
{
lean_dec(x_355);
x_342 = x_358;
x_343 = lean_box(0);
goto block_353;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_361 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_338, x_360, x_341, x_355, x_358, x_357);
lean_dec(x_355);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
lean_dec_ref(x_361);
x_342 = x_362;
x_343 = lean_box(0);
goto block_353;
}
}
else
{
lean_dec(x_355);
lean_dec_ref(x_341);
lean_dec(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_337);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_336;
}
}
block_336:
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_box(12);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 1, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_334);
return x_335;
}
block_353:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
lean_dec_ref(x_344);
lean_inc(x_345);
x_346 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_337, x_338, x_341, x_345, x_3, x_4, x_5);
lean_dec_ref(x_341);
lean_dec_ref(x_338);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_348 = x_346;
} else {
 lean_dec_ref(x_346);
 x_348 = lean_box(0);
}
x_349 = l_Lean_IR_CtorInfo_type(x_337);
if (lean_is_scalar(x_339)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_339;
}
lean_ctor_set(x_350, 0, x_337);
lean_ctor_set(x_350, 1, x_342);
if (lean_is_scalar(x_18)) {
 x_351 = lean_alloc_ctor(0, 4, 0);
} else {
 x_351 = x_18;
}
lean_ctor_set(x_351, 0, x_345);
lean_ctor_set(x_351, 1, x_349);
lean_ctor_set(x_351, 2, x_350);
lean_ctor_set(x_351, 3, x_347);
if (lean_is_scalar(x_348)) {
 x_352 = lean_alloc_ctor(0, 1, 0);
} else {
 x_352 = x_348;
}
lean_ctor_set(x_352, 0, x_351);
return x_352;
}
else
{
lean_dec(x_345);
lean_dec_ref(x_342);
lean_dec(x_339);
lean_dec_ref(x_337);
lean_dec(x_18);
return x_346;
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_325);
lean_dec(x_132);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_363 = lean_ctor_get(x_331, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 x_364 = x_331;
} else {
 lean_dec_ref(x_331);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 1, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_363);
return x_365;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_325);
lean_dec(x_132);
lean_dec(x_127);
x_366 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_368 = x_366;
} else {
 lean_dec_ref(x_366);
 x_368 = lean_box(0);
}
x_369 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_371 = x_369;
} else {
 lean_dec_ref(x_369);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_372 = lean_alloc_ctor(0, 1, 0);
} else {
 x_372 = x_368;
}
lean_ctor_set(x_372, 0, x_324);
x_373 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_373, 0, x_372);
if (lean_is_scalar(x_18)) {
 x_374 = lean_alloc_ctor(0, 4, 0);
} else {
 x_374 = x_18;
}
lean_ctor_set(x_374, 0, x_367);
lean_ctor_set(x_374, 1, x_329);
lean_ctor_set(x_374, 2, x_373);
lean_ctor_set(x_374, 3, x_370);
if (lean_is_scalar(x_371)) {
 x_375 = lean_alloc_ctor(0, 1, 0);
} else {
 x_375 = x_371;
}
lean_ctor_set(x_375, 0, x_374);
return x_375;
}
else
{
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_329);
lean_dec(x_324);
lean_dec(x_18);
return x_369;
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_132);
lean_dec(x_127);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_376 = lean_ctor_get(x_328, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_377 = x_328;
} else {
 lean_dec_ref(x_328);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 1, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_376);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_132);
lean_dec(x_127);
lean_dec(x_18);
x_379 = lean_ctor_get(x_327, 0);
lean_inc(x_379);
lean_dec_ref(x_327);
x_380 = lean_st_ref_take(x_3);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_379, 2);
lean_inc(x_382);
lean_dec(x_379);
x_383 = lean_ctor_get(x_380, 0);
lean_inc_ref(x_383);
x_384 = lean_ctor_get(x_380, 1);
lean_inc_ref(x_384);
x_385 = lean_ctor_get(x_380, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_380, 3);
lean_inc_ref(x_386);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 lean_ctor_release(x_380, 2);
 lean_ctor_release(x_380, 3);
 x_387 = x_380;
} else {
 lean_dec_ref(x_380);
 x_387 = lean_box(0);
}
x_388 = lean_box(0);
x_389 = lean_nat_add(x_381, x_382);
lean_dec(x_382);
lean_dec(x_381);
x_390 = lean_array_get(x_388, x_128, x_389);
lean_dec(x_389);
lean_dec_ref(x_128);
x_391 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_386, x_15, x_390);
if (lean_is_scalar(x_387)) {
 x_392 = lean_alloc_ctor(0, 4, 0);
} else {
 x_392 = x_387;
}
lean_ctor_set(x_392, 0, x_383);
lean_ctor_set(x_392, 1, x_384);
lean_ctor_set(x_392, 2, x_385);
lean_ctor_set(x_392, 3, x_391);
x_393 = lean_st_ref_set(x_3, x_392);
x_394 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_395 = lean_ctor_get(x_326, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_396 = x_326;
} else {
 lean_dec_ref(x_326);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_395);
return x_397;
}
}
}
case 7:
{
uint8_t x_398; 
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_18);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_398 = !lean_is_exclusive(x_142);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_399 = lean_ctor_get(x_142, 0);
lean_dec(x_399);
x_400 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_401 = 1;
x_402 = l_Lean_Name_toString(x_127, x_401);
lean_ctor_set_tag(x_142, 3);
lean_ctor_set(x_142, 0, x_402);
x_403 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_142);
x_404 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_405 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
x_406 = l_Lean_MessageData_ofFormat(x_405);
x_407 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_406, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_407;
}
else
{
lean_object* x_408; uint8_t x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_142);
x_408 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_409 = 1;
x_410 = l_Lean_Name_toString(x_127, x_409);
x_411 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_412 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_412, 0, x_408);
lean_ctor_set(x_412, 1, x_411);
x_413 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_414 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
x_415 = l_Lean_MessageData_ofFormat(x_414);
x_416 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_415, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_416;
}
}
default: 
{
lean_object* x_417; 
lean_dec(x_142);
lean_dec_ref(x_128);
lean_dec(x_18);
x_417 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_127, x_132, x_3, x_4, x_5);
return x_417;
}
}
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec_ref(x_128);
lean_dec(x_18);
x_418 = lean_ctor_get(x_136, 0);
lean_inc(x_418);
lean_dec_ref(x_136);
x_419 = lean_ctor_get(x_418, 3);
lean_inc_ref(x_419);
lean_dec(x_418);
x_420 = lean_array_get_size(x_419);
lean_dec_ref(x_419);
x_421 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_127, x_420, x_132, x_3, x_4, x_5);
return x_421;
}
}
else
{
uint8_t x_422; 
lean_dec(x_132);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_422 = !lean_is_exclusive(x_135);
if (x_422 == 0)
{
return x_135;
}
else
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_135, 0);
lean_inc(x_423);
lean_dec(x_135);
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_423);
return x_424;
}
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec_ref(x_128);
lean_dec(x_18);
x_425 = lean_ctor_get(x_134, 0);
lean_inc(x_425);
lean_dec_ref(x_134);
x_426 = l_Lean_IR_Decl_params(x_425);
lean_dec(x_425);
x_427 = lean_array_get_size(x_426);
lean_dec_ref(x_426);
x_428 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_127, x_427, x_132, x_3, x_4, x_5);
return x_428;
}
}
default: 
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_18);
x_429 = lean_ctor_get(x_20, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_430);
lean_dec_ref(x_20);
x_431 = l_Lean_IR_ToIR_getFVarValue___redArg(x_429, x_3);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec_ref(x_431);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; size_t x_434; size_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
lean_dec_ref(x_432);
x_434 = lean_array_size(x_430);
x_435 = 0;
x_436 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_434, x_435, x_430, x_3);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_438 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(x_1, x_2, x_433, x_437, x_3, x_4, x_5);
return x_438;
}
else
{
lean_object* x_439; 
lean_dec_ref(x_430);
x_439 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5);
return x_439;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_IR_ToIR_lowerLet___closed__2;
x_12 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_11, x_7, x_8, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_ToIR_bindErased___redArg(x_7, x_3);
lean_dec_ref(x_8);
x_9 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
x_16 = l_Lean_IR_toIRType(x_11, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_IR_IRType_boxed(x_17);
lean_dec(x_17);
x_22 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_1, 3, x_20);
lean_ctor_set(x_1, 2, x_22);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lean_IR_IRType_boxed(x_17);
lean_dec(x_17);
x_25 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_25);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_15);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
}
else
{
lean_dec(x_17);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_1);
x_32 = l_Lean_IR_ToIR_bindVar___redArg(x_30, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
lean_inc(x_7);
lean_inc_ref(x_6);
x_34 = l_Lean_IR_toIRType(x_31, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = l_Lean_IR_IRType_boxed(x_35);
lean_dec(x_35);
x_40 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_4);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_37);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_dec(x_35);
lean_dec(x_33);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_36;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_44 = x_34;
} else {
 lean_dec_ref(x_34);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_10, x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_10, x_4);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_4);
x_15 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = l_Lean_IR_ToIR_bindVar___redArg(x_11, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_8);
lean_inc_ref(x_7);
x_17 = l_Lean_IR_toIRType(x_12, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_ToIR_newVar___redArg(x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_IR_ToIR_lowerCode(x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_IR_IRType_boxed(x_18);
lean_dec(x_18);
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_26 = l_Array_extract___redArg(x_5, x_25, x_4);
x_27 = lean_array_get_size(x_5);
x_28 = l_Array_extract___redArg(x_5, x_4, x_27);
x_29 = lean_box(7);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_26);
lean_inc(x_20);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_31);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_16);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_1);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l_Lean_IR_IRType_boxed(x_18);
lean_dec(x_18);
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_36 = l_Array_extract___redArg(x_5, x_35, x_4);
x_37 = lean_array_get_size(x_5);
x_38 = l_Array_extract___redArg(x_5, x_4, x_37);
x_39 = lean_box(7);
x_40 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_36);
lean_inc(x_20);
x_41 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_41, 0, x_20);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_1, 3, x_33);
lean_ctor_set(x_1, 2, x_41);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_16);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_1);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
else
{
uint8_t x_44; 
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_1);
x_49 = l_Lean_IR_ToIR_bindVar___redArg(x_47, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_8);
lean_inc_ref(x_7);
x_51 = l_Lean_IR_toIRType(x_48, x_7, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_IR_ToIR_newVar___redArg(x_6);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_IR_ToIR_lowerCode(x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = l_Lean_IR_IRType_boxed(x_52);
lean_dec(x_52);
x_59 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_60 = l_Array_extract___redArg(x_5, x_59, x_4);
x_61 = lean_array_get_size(x_5);
x_62 = l_Array_extract___redArg(x_5, x_4, x_61);
x_63 = lean_box(7);
x_64 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_64, 0, x_3);
lean_ctor_set(x_64, 1, x_60);
lean_inc(x_54);
x_65 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_62);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_50);
lean_ctor_set(x_66, 1, x_58);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_56);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_54);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_66);
if (lean_is_scalar(x_57)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_57;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_4);
lean_dec(x_3);
return x_55;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_50);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_69 = lean_ctor_get(x_51, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_70 = x_51;
} else {
 lean_dec_ref(x_51);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
x_16 = l_Lean_IR_toIRType(x_11, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_1, 3, x_20);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_1, 3, x_22);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
else
{
lean_dec(x_17);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = l_Lean_IR_ToIR_bindVar___redArg(x_28, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc(x_7);
lean_inc_ref(x_6);
x_32 = l_Lean_IR_toIRType(x_29, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_4);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_35);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_dec(x_33);
lean_dec(x_31);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_34;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_31);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_41 = x_32;
} else {
 lean_dec_ref(x_32);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(7);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_1, 3, x_18);
lean_ctor_set(x_1, 2, x_20);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(7);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_1, 3, x_21);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_15);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
else
{
lean_dec(x_15);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_IR_ToIR_bindVar___redArg(x_25, x_5);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(7);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_4);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_29);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_dec(x_27);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_10, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_IR_ToIR_lowerCode(x_1, x_7, x_8, x_9);
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
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_6 = x_19;
goto _start;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_6, x_22);
lean_dec(x_6);
lean_inc(x_5);
x_24 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_23, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_15);
lean_inc(x_21);
x_27 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_15);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
lean_inc(x_15);
lean_inc(x_21);
x_29 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_15);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_dec(x_5);
return x_24;
}
}
case 3:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_17, 1);
x_32 = lean_ctor_get(x_17, 2);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_6, x_33);
lean_dec(x_6);
lean_inc(x_5);
x_35 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_34, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_2, 2);
x_39 = lean_ctor_get(x_2, 3);
x_40 = lean_nat_add(x_38, x_39);
lean_inc(x_32);
lean_inc(x_15);
lean_inc(x_31);
x_41 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_15);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_37);
lean_ctor_set(x_35, 0, x_41);
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_2, 2);
x_44 = lean_ctor_get(x_2, 3);
x_45 = lean_nat_add(x_43, x_44);
lean_inc(x_32);
lean_inc(x_15);
lean_inc(x_31);
x_46 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_31);
lean_ctor_set(x_46, 3, x_15);
lean_ctor_set(x_46, 4, x_32);
lean_ctor_set(x_46, 5, x_42);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
lean_dec(x_5);
return x_35;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_6, x_48);
lean_dec(x_6);
x_6 = x_49;
goto _start;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_6, x_51);
lean_dec(x_6);
x_6 = x_52;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_8, x_9, x_3, x_4, x_5, x_6);
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
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_6, x_7, x_3, x_4);
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
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_8, x_9, x_3, x_4, x_5, x_6);
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
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerCode(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerAlt(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerLet(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_8, x_3, x_4);
lean_dec_ref(x_9);
x_10 = l_Lean_IR_ToIR_lowerCode(x_2, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
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
x_3 = lean_unsigned_to_nat(333u);
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
x_3 = l_Lean_mkConst(x_2, x_1);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
x_7 = l_Lean_IR_toIRType(x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType___redArg(x_1, x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerResultType___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_10, x_11, x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
lean_inc(x_4);
lean_inc_ref(x_3);
x_15 = l_Lean_IR_ToIR_lowerResultType___redArg(x_7, x_14, x_3, x_4);
lean_dec_ref(x_7);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = l_Lean_IR_ToIR_lowerCode(x_18, x_2, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_23);
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_9);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_9);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_dec(x_9);
x_32 = l_Lean_IR_ToIR_lowerCode(x_31, x_2, x_3, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_13);
lean_ctor_set(x_36, 2, x_16);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_6);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_9, 0);
x_46 = l_List_isEmpty___redArg(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_4);
x_47 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_13);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_9, 0, x_47);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_free_object(x_9);
lean_dec(x_45);
lean_free_object(x_15);
x_48 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_44);
x_49 = l_Lean_IR_ToIR_addDecl___redArg(x_48, x_4);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_49);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_9, 0);
lean_inc(x_56);
lean_dec(x_9);
x_57 = l_List_isEmpty___redArg(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_4);
x_58 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_58, 0, x_6);
lean_ctor_set(x_58, 1, x_13);
lean_ctor_set(x_58, 2, x_55);
lean_ctor_set(x_58, 3, x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_15, 0, x_59);
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_56);
lean_free_object(x_15);
x_60 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_55);
x_61 = l_Lean_IR_ToIR_addDecl___redArg(x_60, x_4);
lean_dec(x_4);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_62 = x_61;
} else {
 lean_dec_ref(x_61);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_15, 0);
lean_inc(x_65);
lean_dec(x_15);
x_66 = lean_ctor_get(x_9, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_67 = x_9;
} else {
 lean_dec_ref(x_9);
 x_67 = lean_box(0);
}
x_68 = l_List_isEmpty___redArg(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_4);
x_69 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_69, 0, x_6);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_66);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
lean_dec(x_66);
x_72 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_65);
x_73 = l_Lean_IR_ToIR_addDecl___redArg(x_72, x_4);
lean_dec(x_4);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_74 = x_73;
} else {
 lean_dec_ref(x_73);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_15);
if (x_77 == 0)
{
return x_15;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_15, 0);
lean_inc(x_78);
lean_dec(x_15);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
return x_12;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_12, 0);
lean_inc(x_81);
lean_dec(x_12);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerDecl(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(x_11, 0, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_IR_ToIR_M_run___redArg(x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 0)
{
x_14 = x_4;
goto block_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec_ref(x_13);
x_20 = lean_array_push(x_4, x_19);
x_14 = x_20;
goto block_18;
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
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
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = l_Lean_IR_toIR___closed__0;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(x_1, x_6, x_7, x_5, x_2, x_3);
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
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_toIR(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse);
l_Lean_IR_ToIR_instMonadFVarSubstStateM = _init_l_Lean_IR_ToIR_instMonadFVarSubstStateM();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstStateM);
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
l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3);
l_Lean_IR_ToIR_getFVarValue___redArg___closed__0 = _init_l_Lean_IR_ToIR_getFVarValue___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_getFVarValue___redArg___closed__0);
l_Lean_IR_ToIR_addDecl___redArg___closed__0 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__0);
l_Lean_IR_ToIR_addDecl___redArg___closed__1 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__1);
l_Lean_IR_ToIR_addDecl___redArg___closed__2 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__2);
l_Lean_IR_ToIR_addDecl___redArg___closed__3 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__3);
l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0);
l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__1 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__1);
l_Lean_IR_ToIR_instInhabitedTranslatedProj_default = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj_default);
l_Lean_IR_ToIR_instInhabitedTranslatedProj = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj);
l_Lean_IR_ToIR_lowerProj___closed__0 = _init_l_Lean_IR_ToIR_lowerProj___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerProj___closed__0);
l_Lean_IR_ToIR_lowerProj___closed__1 = _init_l_Lean_IR_ToIR_lowerProj___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerProj___closed__1);
l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0 = _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0();
lean_mark_persistent(l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3);
l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___closed__0 = _init_l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___closed__0();
lean_mark_persistent(l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___closed__0);
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
l_Lean_IR_ToIR_lowerCode___closed__5 = _init_l_Lean_IR_ToIR_lowerCode___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__5);
l_Lean_IR_ToIR_lowerCode___closed__6 = _init_l_Lean_IR_ToIR_lowerCode___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__6);
l_Lean_IR_ToIR_lowerCode___closed__7 = _init_l_Lean_IR_ToIR_lowerCode___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__7);
l_Lean_IR_ToIR_lowerCode___closed__8 = _init_l_Lean_IR_ToIR_lowerCode___closed__8();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__8);
l_Lean_IR_ToIR_lowerCode___closed__9 = _init_l_Lean_IR_ToIR_lowerCode___closed__9();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__9);
l_Lean_IR_ToIR_lowerCode___closed__10 = _init_l_Lean_IR_ToIR_lowerCode___closed__10();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__10);
l_Lean_IR_ToIR_lowerCode___closed__11 = _init_l_Lean_IR_ToIR_lowerCode___closed__11();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__11);
l_Lean_IR_ToIR_lowerCode___closed__12 = _init_l_Lean_IR_ToIR_lowerCode___closed__12();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__12);
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
