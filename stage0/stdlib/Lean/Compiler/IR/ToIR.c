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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__11;
lean_object* l_Lean_IR_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Lean_IR_IRType_isVoid(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__1;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__1;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__3;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2;
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__15;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__7;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__13;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__9;
static lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody_default__1;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__7;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_BuilderState_ctorIdx(lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM;
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__4;
lean_object* l_Lean_IR_IRType_boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__6;
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__8;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4;
lean_object* l_Lean_IR_getCtorLayout(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__12;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object**);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_IR_nameToIRType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__1;
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIR___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__10;
lean_object* l_Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
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
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
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
x_1 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___lam__0), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___lam__0), 3, 0);
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
x_6 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_7, 3, x_11);
x_12 = lean_st_ref_set(x_2, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 2);
x_22 = lean_ctor_get(x_7, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_23);
x_25 = lean_st_ref_set(x_2, x_24, x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
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
x_6 = l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(x_1, x_2, x_3, x_4, x_5);
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_st_ref_get(x_7, x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_9, 1, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_st_ref_get(x_7, x_15);
lean_dec(x_7);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = 0;
x_10 = l_Lean_Compiler_LCNF_normFVarImp(x_8, x_1, x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_st_ref_get(x_2, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_17 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_16, x_15, x_11);
lean_dec(x_11);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
lean_dec(x_18);
x_21 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_22 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_21, x_20, x_11);
lean_dec(x_11);
lean_dec_ref(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_box(1);
lean_ctor_set(x_4, 0, x_24);
return x_4;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_27);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Lean_Compiler_LCNF_normFVarImp(x_27, x_1, x_28);
lean_dec_ref(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_st_ref_get(x_2, x_26);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_35);
lean_dec(x_32);
x_36 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_37 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_36, x_35, x_30);
lean_dec(x_30);
lean_dec_ref(x_35);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_26);
return x_40;
}
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
x_4 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2, x_3);
lean_dec(x_2);
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
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_8, x_7, x_1);
lean_dec_ref(x_7);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_13, x_12, x_1);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_8, x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_9, x_12);
lean_ctor_set(x_5, 2, x_13);
lean_ctor_set(x_5, 0, x_11);
x_14 = lean_st_ref_set(x_2, x_5, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_19, x_1, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_21, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_22);
x_28 = lean_st_ref_set(x_2, x_27, x_6);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_29);
return x_31;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_9, x_1, x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = lean_st_ref_set(x_3, x_6, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get(x_6, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_19, x_1, x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
x_26 = lean_st_ref_set(x_3, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_17, x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_18);
x_22 = lean_st_ref_set(x_1, x_21, x_5);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_23);
return x_25;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_8, x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_ctor_set(x_5, 2, x_12);
lean_ctor_set(x_5, 1, x_10);
x_13 = lean_st_ref_set(x_2, x_5, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_20);
x_22 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_19, x_1, x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_20, x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_21);
x_26 = lean_st_ref_set(x_2, x_25, x_6);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_27);
return x_29;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_box(1);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_8, x_1, x_9);
lean_ctor_set(x_5, 0, x_10);
x_11 = lean_st_ref_set(x_2, x_5, x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_22 = lean_box(1);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_18, x_1, x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
x_25 = lean_st_ref_set(x_2, x_24, x_6);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
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
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_IR_ToIR_getFVarValue___redArg(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
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
lean_inc(x_6);
x_9 = l_Lean_IR_ToIR_bindVar___redArg(x_6, x_2, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_IR_toIRType(x_7, x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; uint8_t x_40; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_40 = l_Lean_IR_IRType_isVoid(x_13);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_IR_IRType_isErased(x_13);
x_20 = x_41;
goto block_39;
}
else
{
x_20 = x_40;
goto block_39;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_8);
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_15;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
block_39:
{
if (x_20 == 0)
{
lean_dec(x_6);
x_16 = x_14;
goto block_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_st_ref_take(x_2, x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_22, 3);
x_26 = lean_box(0);
x_27 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_25, x_6, x_26);
lean_ctor_set(x_22, 3, x_27);
x_28 = lean_st_ref_set(x_2, x_22, x_23);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_16 = x_29;
goto block_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
x_32 = lean_ctor_get(x_22, 2);
x_33 = lean_ctor_get(x_22, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_34 = lean_box(0);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_33, x_6, x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_st_ref_set(x_2, x_36, x_23);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
x_16 = x_38;
goto block_19;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
x_1 = l_Lean_IR_instInhabitedFnBody_default__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_28 = lean_apply_4(x_27, x_2, x_3, x_4, x_5);
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
x_46 = lean_apply_4(x_45, x_2, x_3, x_4, x_5);
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
x_67 = lean_apply_4(x_66, x_2, x_3, x_4, x_5);
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
static lean_object* _init_l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___closed__0;
x_18 = lean_array_get_borrowed(x_17, x_1, x_6);
x_19 = lean_nat_dec_eq(x_6, x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = l_Lean_IR_ToIR_bindErased___redArg(x_20, x_7, x_8);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_9 = x_3;
x_10 = x_22;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_st_ref_take(x_7, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_4, 2);
x_29 = lean_ctor_get(x_24, 3);
lean_inc(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
lean_inc(x_27);
x_31 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_29, x_27, x_30);
lean_ctor_set(x_24, 3, x_31);
x_32 = lean_st_ref_set(x_7, x_24, x_25);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_9 = x_3;
x_10 = x_33;
goto block_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_4, 2);
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
x_38 = lean_ctor_get(x_24, 2);
x_39 = lean_ctor_get(x_24, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
lean_inc(x_35);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
lean_inc(x_34);
x_41 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_39, x_34, x_40);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_st_ref_set(x_7, x_42, x_25);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_9 = x_3;
x_10 = x_44;
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
x_6 = x_12;
x_8 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_1, x_2, x_3, x_4, x_8, x_11, x_14, x_17);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_62);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_62, 0);
x_64 = lean_ctor_get(x_62, 2);
x_65 = lean_ctor_get(x_62, 3);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_63);
x_66 = l_Lean_IR_hasTrivialStructure_x3f(x_63, x_3, x_4, x_5);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_inc_ref(x_65);
lean_inc(x_64);
lean_inc(x_63);
x_68 = !lean_is_exclusive(x_62);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_62, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_62, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_62, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_62, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec_ref(x_66);
x_74 = l_Lean_IR_ToIR_getFVarValue___redArg(x_64, x_2, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec_ref(x_75);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_63);
x_78 = l_Lean_IR_nameToIRType(x_63, x_3, x_4, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_array_size(x_65);
x_82 = 0;
lean_inc(x_77);
x_83 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_77, x_81, x_82, x_65, x_2, x_3, x_4, x_80);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_ctor_set_tag(x_62, 9);
lean_ctor_set(x_62, 3, x_85);
lean_ctor_set(x_62, 2, x_79);
lean_ctor_set(x_62, 1, x_77);
lean_ctor_set(x_83, 0, x_62);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_83, 0);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_83);
lean_ctor_set_tag(x_62, 9);
lean_ctor_set(x_62, 3, x_86);
lean_ctor_set(x_62, 2, x_79);
lean_ctor_set(x_62, 1, x_77);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_62);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_79);
lean_dec(x_77);
lean_free_object(x_62);
lean_dec(x_63);
x_89 = !lean_is_exclusive(x_83);
if (x_89 == 0)
{
return x_83;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_83, 0);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_83);
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
lean_dec(x_77);
lean_free_object(x_62);
lean_dec_ref(x_65);
lean_dec(x_63);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_78);
if (x_93 == 0)
{
return x_78;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_78, 0);
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_78);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_free_object(x_62);
lean_dec_ref(x_65);
lean_dec(x_63);
x_97 = lean_ctor_get(x_74, 1);
lean_inc(x_97);
lean_dec_ref(x_74);
x_98 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_99 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_98, x_2, x_3, x_4, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_62);
x_100 = lean_ctor_get(x_66, 1);
lean_inc(x_100);
lean_dec_ref(x_66);
x_101 = l_Lean_IR_ToIR_getFVarValue___redArg(x_64, x_2, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec_ref(x_102);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_63);
x_105 = l_Lean_IR_nameToIRType(x_63, x_3, x_4, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; size_t x_108; size_t x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_array_size(x_65);
x_109 = 0;
lean_inc(x_104);
x_110 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_104, x_108, x_109, x_65, x_2, x_3, x_4, x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_114, 0, x_63);
lean_ctor_set(x_114, 1, x_104);
lean_ctor_set(x_114, 2, x_106);
lean_ctor_set(x_114, 3, x_111);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_63);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_104);
lean_dec_ref(x_65);
lean_dec(x_63);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_105, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_105, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_122 = x_105;
} else {
 lean_dec_ref(x_105);
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
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_65);
lean_dec(x_63);
x_124 = lean_ctor_get(x_101, 1);
lean_inc(x_124);
lean_dec_ref(x_101);
x_125 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_126 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_125, x_2, x_3, x_4, x_124);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_66, 1);
lean_inc(x_127);
lean_dec_ref(x_66);
x_128 = lean_ctor_get(x_67, 0);
lean_inc(x_128);
lean_dec_ref(x_67);
x_129 = lean_array_get_size(x_65);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_dec_eq(x_129, x_130);
lean_dec(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_128);
lean_dec_ref(x_62);
x_132 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_133 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_132, x_2, x_3, x_4, x_127);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = l_Lean_IR_ToIR_lowerCode___closed__7;
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_array_get_borrowed(x_134, x_65, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_137 = lean_ctor_get(x_136, 0);
x_138 = lean_ctor_get(x_136, 1);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_136, 2);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_128, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_128, 2);
lean_inc(x_141);
lean_dec(x_128);
x_142 = lean_name_eq(x_137, x_140);
lean_dec(x_140);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_141);
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_62);
x_143 = l_Lean_IR_ToIR_lowerCode___closed__9;
x_144 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_143, x_2, x_3, x_4, x_127);
return x_144;
}
else
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_array_get_size(x_138);
x_146 = lean_nat_dec_lt(x_141, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_62);
x_147 = l_Lean_IR_ToIR_lowerCode___closed__11;
x_148 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_147, x_2, x_3, x_4, x_127);
return x_148;
}
else
{
uint8_t x_149; 
x_149 = lean_nat_dec_lt(x_135, x_145);
if (x_149 == 0)
{
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_138);
lean_dec_ref(x_62);
x_1 = x_139;
x_5 = x_127;
goto _start;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_box(0);
x_152 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_138, x_141, x_151, x_62, x_145, x_135, x_2, x_127);
lean_dec(x_145);
lean_dec_ref(x_62);
lean_dec(x_141);
lean_dec_ref(x_138);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_1 = x_139;
x_5 = x_153;
goto _start;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_128);
lean_dec_ref(x_62);
x_155 = l_Lean_IR_ToIR_lowerCode___closed__12;
x_156 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_155, x_2, x_3, x_4, x_127);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec_ref(x_62);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_66);
if (x_157 == 0)
{
return x_66;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_66, 0);
x_159 = lean_ctor_get(x_66, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_66);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
case 5:
{
uint8_t x_161; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_161 = !lean_is_exclusive(x_1);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_1, 0);
x_163 = l_Lean_IR_ToIR_getFVarValue___redArg(x_162, x_2, x_5);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_163, 0);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_165);
lean_ctor_set(x_163, 0, x_1);
return x_163;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_163, 0);
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_163);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_1, 0);
lean_inc(x_169);
lean_dec(x_1);
x_170 = l_Lean_IR_ToIR_getFVarValue___redArg(x_169, x_2, x_5);
lean_dec(x_2);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_174, 0, x_171);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
}
default: 
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_176 = lean_box(12);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_5);
return x_177;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_2, 2);
x_11 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
x_12 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set_tag(x_5, 3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_2, 2);
x_19 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
x_20 = l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_18);
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
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
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_9 = x_7;
goto block_15;
}
case 2:
{
x_8 = x_5;
x_9 = x_7;
goto block_15;
}
case 3:
{
x_8 = x_5;
x_9 = x_7;
goto block_15;
}
default: 
{
x_8 = x_5;
x_9 = x_7;
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
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_1, x_2, x_3, x_7, x_9, x_10, x_16);
return x_17;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_st_ref_get(x_3, x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_15, 3);
lean_inc_ref(x_19);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 x_20 = x_15;
} else {
 lean_dec_ref(x_15);
 x_20 = lean_box(0);
}
x_21 = 0;
lean_inc(x_18);
x_22 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_19, x_18, x_21);
lean_dec_ref(x_19);
switch (lean_obj_tag(x_22)) {
case 0:
{
uint8_t x_23; 
lean_inc(x_17);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_16);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_IR_ToIR_lowerLitValue(x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_ctor_set_tag(x_22, 11);
lean_ctor_set(x_22, 0, x_29);
if (lean_is_scalar(x_20)) {
 x_34 = lean_alloc_ctor(0, 4, 0);
} else {
 x_34 = x_20;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
lean_ctor_set_tag(x_22, 11);
lean_ctor_set(x_22, 0, x_29);
if (lean_is_scalar(x_20)) {
 x_37 = lean_alloc_ctor(0, 4, 0);
} else {
 x_37 = x_20;
}
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_22);
lean_ctor_set(x_37, 3, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_free_object(x_22);
lean_dec(x_20);
return x_31;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_16);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lean_IR_ToIR_lowerLitValue(x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_50, 0, x_44);
if (lean_is_scalar(x_20)) {
 x_51 = lean_alloc_ctor(0, 4, 0);
} else {
 x_51 = x_20;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_47);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_20);
return x_46;
}
}
}
case 1:
{
lean_object* x_53; 
lean_dec(x_20);
x_53 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_16);
return x_53;
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_17);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_22, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_22, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_22, 2);
lean_inc(x_56);
lean_dec_ref(x_22);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_54);
x_57 = l_Lean_IR_hasTrivialStructure_x3f(x_54, x_4, x_5, x_16);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = l_Lean_IR_ToIR_getFVarValue___redArg(x_56, x_3, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_st_ref_get(x_5, x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
lean_dec(x_65);
x_68 = l_Lean_Environment_find_x3f(x_67, x_54, x_21);
if (lean_obj_tag(x_68) == 0)
{
lean_dec(x_63);
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_66;
goto block_13;
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
if (lean_obj_tag(x_69) == 5)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_70);
lean_dec_ref(x_69);
x_71 = lean_ctor_get(x_70, 4);
lean_inc(x_71);
lean_dec_ref(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_dec(x_63);
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_66;
goto block_13;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 1);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec_ref(x_71);
lean_inc(x_5);
lean_inc_ref(x_4);
x_74 = l_Lean_IR_getCtorLayout(x_73, x_4, x_5, x_66);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_78);
lean_dec(x_75);
x_79 = lean_box(0);
x_80 = lean_array_get(x_79, x_78, x_55);
lean_dec(x_55);
lean_dec_ref(x_78);
x_81 = l_Lean_IR_ToIR_lowerProj(x_63, x_77, x_80);
lean_dec_ref(x_77);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_84);
lean_dec_ref(x_82);
x_85 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_76);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_87);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
if (lean_is_scalar(x_20)) {
 x_91 = lean_alloc_ctor(0, 4, 0);
} else {
 x_91 = x_20;
}
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_83);
lean_ctor_set(x_91, 2, x_84);
lean_ctor_set(x_91, 3, x_90);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
if (lean_is_scalar(x_20)) {
 x_94 = lean_alloc_ctor(0, 4, 0);
} else {
 x_94 = x_20;
}
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_83);
lean_ctor_set(x_94, 2, x_84);
lean_ctor_set(x_94, 3, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_dec(x_86);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_20);
return x_88;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_81);
lean_dec(x_20);
x_96 = l_Lean_IR_ToIR_bindErased___redArg(x_17, x_3, x_76);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_63);
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_99 = !lean_is_exclusive(x_74);
if (x_99 == 0)
{
return x_74;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_74, 0);
x_101 = lean_ctor_get(x_74, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_74);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_dec_ref(x_71);
lean_dec(x_63);
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_66;
goto block_13;
}
}
}
else
{
lean_dec(x_69);
lean_dec(x_63);
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_66;
goto block_13;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_20);
x_103 = lean_ctor_get(x_60, 1);
lean_inc(x_103);
lean_dec_ref(x_60);
x_104 = l_Lean_IR_ToIR_bindErased___redArg(x_17, x_3, x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_54);
lean_dec(x_20);
x_107 = !lean_is_exclusive(x_58);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_58, 0);
x_109 = lean_ctor_get(x_57, 1);
lean_inc(x_109);
lean_dec_ref(x_57);
x_110 = lean_ctor_get(x_108, 2);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_nat_dec_eq(x_110, x_55);
lean_dec(x_55);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_free_object(x_58);
lean_dec(x_56);
x_112 = l_Lean_IR_ToIR_bindErased___redArg(x_17, x_3, x_109);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_113);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_st_ref_take(x_3, x_109);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec_ref(x_115);
x_118 = !lean_is_exclusive(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_116, 3);
lean_ctor_set(x_58, 0, x_56);
x_120 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_119, x_17, x_58);
lean_ctor_set(x_116, 3, x_120);
x_121 = lean_st_ref_set(x_3, x_116, x_117);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_124 = lean_ctor_get(x_116, 0);
x_125 = lean_ctor_get(x_116, 1);
x_126 = lean_ctor_get(x_116, 2);
x_127 = lean_ctor_get(x_116, 3);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_116);
lean_ctor_set(x_58, 0, x_56);
x_128 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_127, x_17, x_58);
x_129 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_125);
lean_ctor_set(x_129, 2, x_126);
lean_ctor_set(x_129, 3, x_128);
x_130 = lean_st_ref_set(x_3, x_129, x_117);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_58, 0);
lean_inc(x_133);
lean_dec(x_58);
x_134 = lean_ctor_get(x_57, 1);
lean_inc(x_134);
lean_dec_ref(x_57);
x_135 = lean_ctor_get(x_133, 2);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_nat_dec_eq(x_135, x_55);
lean_dec(x_55);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_56);
x_137 = l_Lean_IR_ToIR_bindErased___redArg(x_17, x_3, x_134);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_140 = lean_st_ref_take(x_3, x_134);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec_ref(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_141, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 3);
lean_inc_ref(x_146);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 lean_ctor_release(x_141, 3);
 x_147 = x_141;
} else {
 lean_dec_ref(x_141);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_56);
x_149 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_146, x_17, x_148);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 4, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_143);
lean_ctor_set(x_150, 1, x_144);
lean_ctor_set(x_150, 2, x_145);
lean_ctor_set(x_150, 3, x_149);
x_151 = lean_st_ref_set(x_3, x_150, x_142);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_152);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_154 = !lean_is_exclusive(x_57);
if (x_154 == 0)
{
return x_57;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_57, 0);
x_156 = lean_ctor_get(x_57, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_57);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
case 3:
{
lean_object* x_158; lean_object* x_159; size_t x_160; size_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_158 = lean_ctor_get(x_22, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_159);
lean_dec_ref(x_22);
x_160 = lean_array_size(x_159);
x_161 = 0;
lean_inc_ref(x_159);
x_162 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_160, x_161, x_159, x_3, x_16);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec_ref(x_162);
lean_inc(x_158);
x_165 = l_Lean_IR_ToIR_findDecl___redArg(x_158, x_5, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_165);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_165, 1);
x_169 = lean_ctor_get(x_165, 0);
lean_dec(x_169);
lean_inc(x_158);
x_170 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_158, x_5, x_168);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = lean_st_ref_get(x_5, x_172);
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_173, 1);
x_177 = lean_ctor_get(x_175, 0);
lean_inc_ref(x_177);
lean_dec(x_175);
lean_inc(x_158);
x_178 = l_Lean_Environment_find_x3f(x_177, x_158, x_21);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
lean_free_object(x_173);
lean_free_object(x_165);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_179 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_180 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_179, x_3, x_4, x_5, x_176);
return x_180;
}
else
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_178);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_178, 0);
switch (lean_obj_tag(x_182)) {
case 0:
{
uint8_t x_183; 
lean_free_object(x_178);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_182, 0);
lean_dec(x_184);
x_185 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_186 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_187 = 1;
x_188 = l_Lean_Name_toString(x_158, x_187);
lean_ctor_set_tag(x_182, 3);
lean_ctor_set(x_182, 0, x_188);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_182);
lean_ctor_set(x_173, 0, x_186);
x_189 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_189);
lean_ctor_set(x_165, 0, x_173);
x_190 = l_Lean_MessageData_ofFormat(x_165);
x_191 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_185, x_190, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_182);
x_192 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_193 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_194 = 1;
x_195 = l_Lean_Name_toString(x_158, x_194);
x_196 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_196);
lean_ctor_set(x_173, 0, x_193);
x_197 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_197);
lean_ctor_set(x_165, 0, x_173);
x_198 = l_Lean_MessageData_ofFormat(x_165);
x_199 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_192, x_198, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_199;
}
}
case 2:
{
uint8_t x_200; 
lean_free_object(x_178);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_200 = !lean_is_exclusive(x_182);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_182, 0);
lean_dec(x_201);
x_202 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_203 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_204 = 1;
x_205 = l_Lean_Name_toString(x_158, x_204);
lean_ctor_set_tag(x_182, 3);
lean_ctor_set(x_182, 0, x_205);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_182);
lean_ctor_set(x_173, 0, x_203);
x_206 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_206);
lean_ctor_set(x_165, 0, x_173);
x_207 = l_Lean_MessageData_ofFormat(x_165);
x_208 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_202, x_207, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_182);
x_209 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_210 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_211 = 1;
x_212 = l_Lean_Name_toString(x_158, x_211);
x_213 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_213);
lean_ctor_set(x_173, 0, x_210);
x_214 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_214);
lean_ctor_set(x_165, 0, x_173);
x_215 = l_Lean_MessageData_ofFormat(x_165);
x_216 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_209, x_215, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_216;
}
}
case 4:
{
uint8_t x_217; 
lean_free_object(x_178);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_217 = !lean_is_exclusive(x_182);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_182, 0);
lean_dec(x_218);
x_219 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_220 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_221 = 1;
x_222 = l_Lean_Name_toString(x_158, x_221);
lean_ctor_set_tag(x_182, 3);
lean_ctor_set(x_182, 0, x_222);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_182);
lean_ctor_set(x_173, 0, x_220);
x_223 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_223);
lean_ctor_set(x_165, 0, x_173);
x_224 = l_Lean_MessageData_ofFormat(x_165);
x_225 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_219, x_224, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_182);
x_226 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_227 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_228 = 1;
x_229 = l_Lean_Name_toString(x_158, x_228);
x_230 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_230);
lean_ctor_set(x_173, 0, x_227);
x_231 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_231);
lean_ctor_set(x_165, 0, x_173);
x_232 = l_Lean_MessageData_ofFormat(x_165);
x_233 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_226, x_232, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_233;
}
}
case 5:
{
uint8_t x_234; 
lean_free_object(x_178);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_234 = !lean_is_exclusive(x_182);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_235 = lean_ctor_get(x_182, 0);
lean_dec(x_235);
x_236 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_237 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_238 = 1;
x_239 = l_Lean_Name_toString(x_158, x_238);
lean_ctor_set_tag(x_182, 3);
lean_ctor_set(x_182, 0, x_239);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_182);
lean_ctor_set(x_173, 0, x_237);
x_240 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_240);
lean_ctor_set(x_165, 0, x_173);
x_241 = l_Lean_MessageData_ofFormat(x_165);
x_242 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_236, x_241, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_182);
x_243 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_244 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_245 = 1;
x_246 = l_Lean_Name_toString(x_158, x_245);
x_247 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_247);
lean_ctor_set(x_173, 0, x_244);
x_248 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_248);
lean_ctor_set(x_165, 0, x_173);
x_249 = l_Lean_MessageData_ofFormat(x_165);
x_250 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_243, x_249, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_250;
}
}
case 6:
{
uint8_t x_251; 
lean_free_object(x_173);
lean_free_object(x_165);
lean_inc(x_17);
lean_dec_ref(x_1);
x_251 = !lean_is_exclusive(x_182);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_182, 0);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_252, 3);
lean_inc(x_255);
lean_dec_ref(x_252);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_253);
x_256 = l_Lean_IR_hasTrivialStructure_x3f(x_253, x_4, x_5, x_176);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
lean_dec_ref(x_159);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec_ref(x_256);
lean_inc(x_5);
lean_inc_ref(x_4);
x_259 = l_Lean_IR_nameToIRType(x_253, x_4, x_5, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec_ref(x_259);
x_262 = l_Lean_IR_IRType_isScalar(x_260);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_260);
lean_dec(x_254);
lean_free_object(x_182);
lean_free_object(x_178);
lean_inc(x_5);
lean_inc_ref(x_4);
x_263 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_261);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
x_270 = lean_ctor_get(x_264, 0);
lean_inc_ref(x_270);
x_271 = lean_ctor_get(x_264, 1);
lean_inc_ref(x_271);
lean_dec(x_264);
x_272 = lean_array_get_size(x_163);
x_273 = l_Array_extract___redArg(x_163, x_255, x_272);
lean_dec(x_163);
x_301 = lean_array_get_size(x_273);
x_302 = lean_array_get_size(x_271);
x_303 = lean_nat_dec_eq(x_301, x_302);
lean_dec(x_301);
if (x_303 == 0)
{
lean_dec(x_302);
lean_dec_ref(x_273);
lean_dec_ref(x_271);
lean_dec_ref(x_270);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_269;
}
else
{
if (x_262 == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
lean_dec(x_266);
x_304 = lean_unsigned_to_nat(0u);
x_305 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_306 = lean_nat_dec_lt(x_304, x_302);
if (x_306 == 0)
{
lean_dec(x_302);
x_274 = x_305;
x_275 = x_265;
goto block_300;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_307 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_308 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_271, x_307, x_273, x_302, x_305, x_304, x_265);
lean_dec(x_302);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec_ref(x_308);
x_274 = x_309;
x_275 = x_310;
goto block_300;
}
}
else
{
lean_dec(x_302);
lean_dec_ref(x_273);
lean_dec_ref(x_271);
lean_dec_ref(x_270);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_269;
}
}
block_269:
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_box(12);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_265);
return x_268;
}
block_300:
{
lean_object* x_276; uint8_t x_277; 
x_276 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_275);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
x_280 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_270, x_271, x_273, x_278, x_3, x_4, x_5, x_279);
lean_dec_ref(x_273);
lean_dec_ref(x_271);
if (lean_obj_tag(x_280) == 0)
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = l_Lean_IR_CtorInfo_type(x_270);
lean_ctor_set(x_276, 1, x_274);
lean_ctor_set(x_276, 0, x_270);
if (lean_is_scalar(x_20)) {
 x_284 = lean_alloc_ctor(0, 4, 0);
} else {
 x_284 = x_20;
}
lean_ctor_set(x_284, 0, x_278);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_276);
lean_ctor_set(x_284, 3, x_282);
lean_ctor_set(x_280, 0, x_284);
return x_280;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_285 = lean_ctor_get(x_280, 0);
x_286 = lean_ctor_get(x_280, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_280);
x_287 = l_Lean_IR_CtorInfo_type(x_270);
lean_ctor_set(x_276, 1, x_274);
lean_ctor_set(x_276, 0, x_270);
if (lean_is_scalar(x_20)) {
 x_288 = lean_alloc_ctor(0, 4, 0);
} else {
 x_288 = x_20;
}
lean_ctor_set(x_288, 0, x_278);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_288, 2, x_276);
lean_ctor_set(x_288, 3, x_285);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
return x_289;
}
}
else
{
lean_free_object(x_276);
lean_dec(x_278);
lean_dec_ref(x_274);
lean_dec_ref(x_270);
lean_dec(x_20);
return x_280;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_276, 0);
x_291 = lean_ctor_get(x_276, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_276);
lean_inc(x_290);
x_292 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_270, x_271, x_273, x_290, x_3, x_4, x_5, x_291);
lean_dec_ref(x_273);
lean_dec_ref(x_271);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
x_296 = l_Lean_IR_CtorInfo_type(x_270);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_270);
lean_ctor_set(x_297, 1, x_274);
if (lean_is_scalar(x_20)) {
 x_298 = lean_alloc_ctor(0, 4, 0);
} else {
 x_298 = x_20;
}
lean_ctor_set(x_298, 0, x_290);
lean_ctor_set(x_298, 1, x_296);
lean_ctor_set(x_298, 2, x_297);
lean_ctor_set(x_298, 3, x_293);
if (lean_is_scalar(x_295)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_295;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_294);
return x_299;
}
else
{
lean_dec(x_290);
lean_dec_ref(x_274);
lean_dec_ref(x_270);
lean_dec(x_20);
return x_292;
}
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_255);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_311 = !lean_is_exclusive(x_263);
if (x_311 == 0)
{
return x_263;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_263, 0);
x_313 = lean_ctor_get(x_263, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_263);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_255);
lean_dec(x_163);
lean_dec(x_158);
x_315 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_261);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec_ref(x_315);
x_318 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_317);
if (lean_obj_tag(x_318) == 0)
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_318, 0);
lean_ctor_set_tag(x_182, 0);
lean_ctor_set(x_182, 0, x_254);
lean_ctor_set_tag(x_178, 11);
if (lean_is_scalar(x_20)) {
 x_321 = lean_alloc_ctor(0, 4, 0);
} else {
 x_321 = x_20;
}
lean_ctor_set(x_321, 0, x_316);
lean_ctor_set(x_321, 1, x_260);
lean_ctor_set(x_321, 2, x_178);
lean_ctor_set(x_321, 3, x_320);
lean_ctor_set(x_318, 0, x_321);
return x_318;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_318, 0);
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_318);
lean_ctor_set_tag(x_182, 0);
lean_ctor_set(x_182, 0, x_254);
lean_ctor_set_tag(x_178, 11);
if (lean_is_scalar(x_20)) {
 x_324 = lean_alloc_ctor(0, 4, 0);
} else {
 x_324 = x_20;
}
lean_ctor_set(x_324, 0, x_316);
lean_ctor_set(x_324, 1, x_260);
lean_ctor_set(x_324, 2, x_178);
lean_ctor_set(x_324, 3, x_322);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
lean_dec(x_316);
lean_dec(x_260);
lean_dec(x_254);
lean_free_object(x_182);
lean_free_object(x_178);
lean_dec(x_20);
return x_318;
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_255);
lean_dec(x_254);
lean_free_object(x_182);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_326 = !lean_is_exclusive(x_259);
if (x_326 == 0)
{
return x_259;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_259, 0);
x_328 = lean_ctor_get(x_259, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_259);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_free_object(x_182);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_330 = lean_ctor_get(x_256, 1);
lean_inc(x_330);
lean_dec_ref(x_256);
x_331 = lean_ctor_get(x_257, 0);
lean_inc(x_331);
lean_dec_ref(x_257);
x_332 = lean_st_ref_take(x_3, x_330);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec_ref(x_332);
x_335 = lean_ctor_get(x_331, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_331, 2);
lean_inc(x_336);
lean_dec(x_331);
x_337 = !lean_is_exclusive(x_333);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_338 = lean_ctor_get(x_333, 3);
x_339 = lean_box(0);
x_340 = lean_nat_add(x_335, x_336);
lean_dec(x_336);
lean_dec(x_335);
x_341 = lean_array_get(x_339, x_159, x_340);
lean_dec(x_340);
lean_dec_ref(x_159);
x_342 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_338, x_17, x_341);
lean_ctor_set(x_333, 3, x_342);
x_343 = lean_st_ref_set(x_3, x_333, x_334);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec_ref(x_343);
x_345 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_344);
return x_345;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_346 = lean_ctor_get(x_333, 0);
x_347 = lean_ctor_get(x_333, 1);
x_348 = lean_ctor_get(x_333, 2);
x_349 = lean_ctor_get(x_333, 3);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_333);
x_350 = lean_box(0);
x_351 = lean_nat_add(x_335, x_336);
lean_dec(x_336);
lean_dec(x_335);
x_352 = lean_array_get(x_350, x_159, x_351);
lean_dec(x_351);
lean_dec_ref(x_159);
x_353 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_349, x_17, x_352);
x_354 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_354, 0, x_346);
lean_ctor_set(x_354, 1, x_347);
lean_ctor_set(x_354, 2, x_348);
lean_ctor_set(x_354, 3, x_353);
x_355 = lean_st_ref_set(x_3, x_354, x_334);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec_ref(x_355);
x_357 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_356);
return x_357;
}
}
}
else
{
uint8_t x_358; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_free_object(x_182);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_358 = !lean_is_exclusive(x_256);
if (x_358 == 0)
{
return x_256;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_256, 0);
x_360 = lean_ctor_get(x_256, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_256);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_362 = lean_ctor_get(x_182, 0);
lean_inc(x_362);
lean_dec(x_182);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_362, 3);
lean_inc(x_365);
lean_dec_ref(x_362);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_363);
x_366 = l_Lean_IR_hasTrivialStructure_x3f(x_363, x_4, x_5, x_176);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; 
lean_dec_ref(x_159);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec_ref(x_366);
lean_inc(x_5);
lean_inc_ref(x_4);
x_369 = l_Lean_IR_nameToIRType(x_363, x_4, x_5, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec_ref(x_369);
x_372 = l_Lean_IR_IRType_isScalar(x_370);
if (x_372 == 0)
{
lean_object* x_373; 
lean_dec(x_370);
lean_dec(x_364);
lean_free_object(x_178);
lean_inc(x_5);
lean_inc_ref(x_4);
x_373 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_371);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
x_380 = lean_ctor_get(x_374, 0);
lean_inc_ref(x_380);
x_381 = lean_ctor_get(x_374, 1);
lean_inc_ref(x_381);
lean_dec(x_374);
x_382 = lean_array_get_size(x_163);
x_383 = l_Array_extract___redArg(x_163, x_365, x_382);
lean_dec(x_163);
x_399 = lean_array_get_size(x_383);
x_400 = lean_array_get_size(x_381);
x_401 = lean_nat_dec_eq(x_399, x_400);
lean_dec(x_399);
if (x_401 == 0)
{
lean_dec(x_400);
lean_dec_ref(x_383);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_379;
}
else
{
if (x_372 == 0)
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; 
lean_dec(x_376);
x_402 = lean_unsigned_to_nat(0u);
x_403 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_404 = lean_nat_dec_lt(x_402, x_400);
if (x_404 == 0)
{
lean_dec(x_400);
x_384 = x_403;
x_385 = x_375;
goto block_398;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_406 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_381, x_405, x_383, x_400, x_403, x_402, x_375);
lean_dec(x_400);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec_ref(x_406);
x_384 = x_407;
x_385 = x_408;
goto block_398;
}
}
else
{
lean_dec(x_400);
lean_dec_ref(x_383);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_379;
}
}
block_379:
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_box(12);
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_375);
return x_378;
}
block_398:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_386 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_389 = x_386;
} else {
 lean_dec_ref(x_386);
 x_389 = lean_box(0);
}
lean_inc(x_387);
x_390 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_380, x_381, x_383, x_387, x_3, x_4, x_5, x_388);
lean_dec_ref(x_383);
lean_dec_ref(x_381);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_393 = x_390;
} else {
 lean_dec_ref(x_390);
 x_393 = lean_box(0);
}
x_394 = l_Lean_IR_CtorInfo_type(x_380);
if (lean_is_scalar(x_389)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_389;
}
lean_ctor_set(x_395, 0, x_380);
lean_ctor_set(x_395, 1, x_384);
if (lean_is_scalar(x_20)) {
 x_396 = lean_alloc_ctor(0, 4, 0);
} else {
 x_396 = x_20;
}
lean_ctor_set(x_396, 0, x_387);
lean_ctor_set(x_396, 1, x_394);
lean_ctor_set(x_396, 2, x_395);
lean_ctor_set(x_396, 3, x_391);
if (lean_is_scalar(x_393)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_393;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_392);
return x_397;
}
else
{
lean_dec(x_389);
lean_dec(x_387);
lean_dec_ref(x_384);
lean_dec_ref(x_380);
lean_dec(x_20);
return x_390;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_365);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_409 = lean_ctor_get(x_373, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_373, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_411 = x_373;
} else {
 lean_dec_ref(x_373);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
return x_412;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_365);
lean_dec(x_163);
lean_dec(x_158);
x_413 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_371);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec_ref(x_413);
x_416 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_419 = x_416;
} else {
 lean_dec_ref(x_416);
 x_419 = lean_box(0);
}
x_420 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_420, 0, x_364);
lean_ctor_set_tag(x_178, 11);
lean_ctor_set(x_178, 0, x_420);
if (lean_is_scalar(x_20)) {
 x_421 = lean_alloc_ctor(0, 4, 0);
} else {
 x_421 = x_20;
}
lean_ctor_set(x_421, 0, x_414);
lean_ctor_set(x_421, 1, x_370);
lean_ctor_set(x_421, 2, x_178);
lean_ctor_set(x_421, 3, x_417);
if (lean_is_scalar(x_419)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_419;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_418);
return x_422;
}
else
{
lean_dec(x_414);
lean_dec(x_370);
lean_dec(x_364);
lean_free_object(x_178);
lean_dec(x_20);
return x_416;
}
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_365);
lean_dec(x_364);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_423 = lean_ctor_get(x_369, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_369, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_425 = x_369;
} else {
 lean_dec_ref(x_369);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_365);
lean_dec(x_364);
lean_dec(x_363);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_427 = lean_ctor_get(x_366, 1);
lean_inc(x_427);
lean_dec_ref(x_366);
x_428 = lean_ctor_get(x_367, 0);
lean_inc(x_428);
lean_dec_ref(x_367);
x_429 = lean_st_ref_take(x_3, x_427);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec_ref(x_429);
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_428, 2);
lean_inc(x_433);
lean_dec(x_428);
x_434 = lean_ctor_get(x_430, 0);
lean_inc_ref(x_434);
x_435 = lean_ctor_get(x_430, 1);
lean_inc_ref(x_435);
x_436 = lean_ctor_get(x_430, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_430, 3);
lean_inc_ref(x_437);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_438 = x_430;
} else {
 lean_dec_ref(x_430);
 x_438 = lean_box(0);
}
x_439 = lean_box(0);
x_440 = lean_nat_add(x_432, x_433);
lean_dec(x_433);
lean_dec(x_432);
x_441 = lean_array_get(x_439, x_159, x_440);
lean_dec(x_440);
lean_dec_ref(x_159);
x_442 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_437, x_17, x_441);
if (lean_is_scalar(x_438)) {
 x_443 = lean_alloc_ctor(0, 4, 0);
} else {
 x_443 = x_438;
}
lean_ctor_set(x_443, 0, x_434);
lean_ctor_set(x_443, 1, x_435);
lean_ctor_set(x_443, 2, x_436);
lean_ctor_set(x_443, 3, x_442);
x_444 = lean_st_ref_set(x_3, x_443, x_431);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec_ref(x_444);
x_446 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_445);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_365);
lean_dec(x_364);
lean_dec(x_363);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_447 = lean_ctor_get(x_366, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_366, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_449 = x_366;
} else {
 lean_dec_ref(x_366);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_448);
return x_450;
}
}
}
case 7:
{
uint8_t x_451; 
lean_free_object(x_178);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_451 = !lean_is_exclusive(x_182);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_452 = lean_ctor_get(x_182, 0);
lean_dec(x_452);
x_453 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_454 = 1;
x_455 = l_Lean_Name_toString(x_158, x_454);
lean_ctor_set_tag(x_182, 3);
lean_ctor_set(x_182, 0, x_455);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_182);
lean_ctor_set(x_173, 0, x_453);
x_456 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_456);
lean_ctor_set(x_165, 0, x_173);
x_457 = l_Lean_MessageData_ofFormat(x_165);
x_458 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_457, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_458;
}
else
{
lean_object* x_459; uint8_t x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_182);
x_459 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_460 = 1;
x_461 = l_Lean_Name_toString(x_158, x_460);
x_462 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_462);
lean_ctor_set(x_173, 0, x_459);
x_463 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_463);
lean_ctor_set(x_165, 0, x_173);
x_464 = l_Lean_MessageData_ofFormat(x_165);
x_465 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_464, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_465;
}
}
default: 
{
lean_object* x_466; 
lean_free_object(x_178);
lean_dec(x_182);
lean_free_object(x_173);
lean_free_object(x_165);
lean_dec_ref(x_159);
lean_dec(x_20);
x_466 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_158, x_163, x_3, x_4, x_5, x_176);
return x_466;
}
}
}
else
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_178, 0);
lean_inc(x_467);
lean_dec(x_178);
switch (lean_obj_tag(x_467)) {
case 0:
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 x_468 = x_467;
} else {
 lean_dec_ref(x_467);
 x_468 = lean_box(0);
}
x_469 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_470 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_471 = 1;
x_472 = l_Lean_Name_toString(x_158, x_471);
if (lean_is_scalar(x_468)) {
 x_473 = lean_alloc_ctor(3, 1, 0);
} else {
 x_473 = x_468;
 lean_ctor_set_tag(x_473, 3);
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_473);
lean_ctor_set(x_173, 0, x_470);
x_474 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_474);
lean_ctor_set(x_165, 0, x_173);
x_475 = l_Lean_MessageData_ofFormat(x_165);
x_476 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_469, x_475, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_476;
}
case 2:
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 x_477 = x_467;
} else {
 lean_dec_ref(x_467);
 x_477 = lean_box(0);
}
x_478 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_479 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_480 = 1;
x_481 = l_Lean_Name_toString(x_158, x_480);
if (lean_is_scalar(x_477)) {
 x_482 = lean_alloc_ctor(3, 1, 0);
} else {
 x_482 = x_477;
 lean_ctor_set_tag(x_482, 3);
}
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_482);
lean_ctor_set(x_173, 0, x_479);
x_483 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_483);
lean_ctor_set(x_165, 0, x_173);
x_484 = l_Lean_MessageData_ofFormat(x_165);
x_485 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_478, x_484, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_485;
}
case 4:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 x_486 = x_467;
} else {
 lean_dec_ref(x_467);
 x_486 = lean_box(0);
}
x_487 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_488 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_489 = 1;
x_490 = l_Lean_Name_toString(x_158, x_489);
if (lean_is_scalar(x_486)) {
 x_491 = lean_alloc_ctor(3, 1, 0);
} else {
 x_491 = x_486;
 lean_ctor_set_tag(x_491, 3);
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_491);
lean_ctor_set(x_173, 0, x_488);
x_492 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_492);
lean_ctor_set(x_165, 0, x_173);
x_493 = l_Lean_MessageData_ofFormat(x_165);
x_494 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_487, x_493, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_494;
}
case 5:
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 x_495 = x_467;
} else {
 lean_dec_ref(x_467);
 x_495 = lean_box(0);
}
x_496 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_497 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_498 = 1;
x_499 = l_Lean_Name_toString(x_158, x_498);
if (lean_is_scalar(x_495)) {
 x_500 = lean_alloc_ctor(3, 1, 0);
} else {
 x_500 = x_495;
 lean_ctor_set_tag(x_500, 3);
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_500);
lean_ctor_set(x_173, 0, x_497);
x_501 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_501);
lean_ctor_set(x_165, 0, x_173);
x_502 = l_Lean_MessageData_ofFormat(x_165);
x_503 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_496, x_502, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_503;
}
case 6:
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_free_object(x_173);
lean_free_object(x_165);
lean_inc(x_17);
lean_dec_ref(x_1);
x_504 = lean_ctor_get(x_467, 0);
lean_inc_ref(x_504);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 x_505 = x_467;
} else {
 lean_dec_ref(x_467);
 x_505 = lean_box(0);
}
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_504, 2);
lean_inc(x_507);
x_508 = lean_ctor_get(x_504, 3);
lean_inc(x_508);
lean_dec_ref(x_504);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_506);
x_509 = l_Lean_IR_hasTrivialStructure_x3f(x_506, x_4, x_5, x_176);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; 
lean_dec_ref(x_159);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
lean_dec_ref(x_509);
lean_inc(x_5);
lean_inc_ref(x_4);
x_512 = l_Lean_IR_nameToIRType(x_506, x_4, x_5, x_511);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec_ref(x_512);
x_515 = l_Lean_IR_IRType_isScalar(x_513);
if (x_515 == 0)
{
lean_object* x_516; 
lean_dec(x_513);
lean_dec(x_507);
lean_dec(x_505);
lean_inc(x_5);
lean_inc_ref(x_4);
x_516 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_514);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_542; lean_object* x_543; uint8_t x_544; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_519 = x_516;
} else {
 lean_dec_ref(x_516);
 x_519 = lean_box(0);
}
x_523 = lean_ctor_get(x_517, 0);
lean_inc_ref(x_523);
x_524 = lean_ctor_get(x_517, 1);
lean_inc_ref(x_524);
lean_dec(x_517);
x_525 = lean_array_get_size(x_163);
x_526 = l_Array_extract___redArg(x_163, x_508, x_525);
lean_dec(x_163);
x_542 = lean_array_get_size(x_526);
x_543 = lean_array_get_size(x_524);
x_544 = lean_nat_dec_eq(x_542, x_543);
lean_dec(x_542);
if (x_544 == 0)
{
lean_dec(x_543);
lean_dec_ref(x_526);
lean_dec_ref(x_524);
lean_dec_ref(x_523);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_522;
}
else
{
if (x_515 == 0)
{
lean_object* x_545; lean_object* x_546; uint8_t x_547; 
lean_dec(x_519);
x_545 = lean_unsigned_to_nat(0u);
x_546 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_547 = lean_nat_dec_lt(x_545, x_543);
if (x_547 == 0)
{
lean_dec(x_543);
x_527 = x_546;
x_528 = x_518;
goto block_541;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_548 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_549 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_524, x_548, x_526, x_543, x_546, x_545, x_518);
lean_dec(x_543);
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec_ref(x_549);
x_527 = x_550;
x_528 = x_551;
goto block_541;
}
}
else
{
lean_dec(x_543);
lean_dec_ref(x_526);
lean_dec_ref(x_524);
lean_dec_ref(x_523);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_522;
}
}
block_522:
{
lean_object* x_520; lean_object* x_521; 
x_520 = lean_box(12);
if (lean_is_scalar(x_519)) {
 x_521 = lean_alloc_ctor(0, 2, 0);
} else {
 x_521 = x_519;
}
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_518);
return x_521;
}
block_541:
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_529 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_528);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_532 = x_529;
} else {
 lean_dec_ref(x_529);
 x_532 = lean_box(0);
}
lean_inc(x_530);
x_533 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_523, x_524, x_526, x_530, x_3, x_4, x_5, x_531);
lean_dec_ref(x_526);
lean_dec_ref(x_524);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_536 = x_533;
} else {
 lean_dec_ref(x_533);
 x_536 = lean_box(0);
}
x_537 = l_Lean_IR_CtorInfo_type(x_523);
if (lean_is_scalar(x_532)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_532;
}
lean_ctor_set(x_538, 0, x_523);
lean_ctor_set(x_538, 1, x_527);
if (lean_is_scalar(x_20)) {
 x_539 = lean_alloc_ctor(0, 4, 0);
} else {
 x_539 = x_20;
}
lean_ctor_set(x_539, 0, x_530);
lean_ctor_set(x_539, 1, x_537);
lean_ctor_set(x_539, 2, x_538);
lean_ctor_set(x_539, 3, x_534);
if (lean_is_scalar(x_536)) {
 x_540 = lean_alloc_ctor(0, 2, 0);
} else {
 x_540 = x_536;
}
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_535);
return x_540;
}
else
{
lean_dec(x_532);
lean_dec(x_530);
lean_dec_ref(x_527);
lean_dec_ref(x_523);
lean_dec(x_20);
return x_533;
}
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_508);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_552 = lean_ctor_get(x_516, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_516, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_554 = x_516;
} else {
 lean_dec_ref(x_516);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_552);
lean_ctor_set(x_555, 1, x_553);
return x_555;
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_508);
lean_dec(x_163);
lean_dec(x_158);
x_556 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_514);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec_ref(x_556);
x_559 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_558);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_562 = x_559;
} else {
 lean_dec_ref(x_559);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_563 = lean_alloc_ctor(0, 1, 0);
} else {
 x_563 = x_505;
 lean_ctor_set_tag(x_563, 0);
}
lean_ctor_set(x_563, 0, x_507);
x_564 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_564, 0, x_563);
if (lean_is_scalar(x_20)) {
 x_565 = lean_alloc_ctor(0, 4, 0);
} else {
 x_565 = x_20;
}
lean_ctor_set(x_565, 0, x_557);
lean_ctor_set(x_565, 1, x_513);
lean_ctor_set(x_565, 2, x_564);
lean_ctor_set(x_565, 3, x_560);
if (lean_is_scalar(x_562)) {
 x_566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_566 = x_562;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_561);
return x_566;
}
else
{
lean_dec(x_557);
lean_dec(x_513);
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_20);
return x_559;
}
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_567 = lean_ctor_get(x_512, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_512, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_569 = x_512;
} else {
 lean_dec_ref(x_512);
 x_569 = lean_box(0);
}
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_567);
lean_ctor_set(x_570, 1, x_568);
return x_570;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_571 = lean_ctor_get(x_509, 1);
lean_inc(x_571);
lean_dec_ref(x_509);
x_572 = lean_ctor_get(x_510, 0);
lean_inc(x_572);
lean_dec_ref(x_510);
x_573 = lean_st_ref_take(x_3, x_571);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec_ref(x_573);
x_576 = lean_ctor_get(x_572, 1);
lean_inc(x_576);
x_577 = lean_ctor_get(x_572, 2);
lean_inc(x_577);
lean_dec(x_572);
x_578 = lean_ctor_get(x_574, 0);
lean_inc_ref(x_578);
x_579 = lean_ctor_get(x_574, 1);
lean_inc_ref(x_579);
x_580 = lean_ctor_get(x_574, 2);
lean_inc(x_580);
x_581 = lean_ctor_get(x_574, 3);
lean_inc_ref(x_581);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 lean_ctor_release(x_574, 2);
 lean_ctor_release(x_574, 3);
 x_582 = x_574;
} else {
 lean_dec_ref(x_574);
 x_582 = lean_box(0);
}
x_583 = lean_box(0);
x_584 = lean_nat_add(x_576, x_577);
lean_dec(x_577);
lean_dec(x_576);
x_585 = lean_array_get(x_583, x_159, x_584);
lean_dec(x_584);
lean_dec_ref(x_159);
x_586 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_581, x_17, x_585);
if (lean_is_scalar(x_582)) {
 x_587 = lean_alloc_ctor(0, 4, 0);
} else {
 x_587 = x_582;
}
lean_ctor_set(x_587, 0, x_578);
lean_ctor_set(x_587, 1, x_579);
lean_ctor_set(x_587, 2, x_580);
lean_ctor_set(x_587, 3, x_586);
x_588 = lean_st_ref_set(x_3, x_587, x_575);
x_589 = lean_ctor_get(x_588, 1);
lean_inc(x_589);
lean_dec_ref(x_588);
x_590 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_589);
return x_590;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_591 = lean_ctor_get(x_509, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_509, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_593 = x_509;
} else {
 lean_dec_ref(x_509);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
}
case 7:
{
lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 x_595 = x_467;
} else {
 lean_dec_ref(x_467);
 x_595 = lean_box(0);
}
x_596 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_597 = 1;
x_598 = l_Lean_Name_toString(x_158, x_597);
if (lean_is_scalar(x_595)) {
 x_599 = lean_alloc_ctor(3, 1, 0);
} else {
 x_599 = x_595;
 lean_ctor_set_tag(x_599, 3);
}
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_599);
lean_ctor_set(x_173, 0, x_596);
x_600 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_600);
lean_ctor_set(x_165, 0, x_173);
x_601 = l_Lean_MessageData_ofFormat(x_165);
x_602 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_601, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_602;
}
default: 
{
lean_object* x_603; 
lean_dec(x_467);
lean_free_object(x_173);
lean_free_object(x_165);
lean_dec_ref(x_159);
lean_dec(x_20);
x_603 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_158, x_163, x_3, x_4, x_5, x_176);
return x_603;
}
}
}
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_604 = lean_ctor_get(x_173, 0);
x_605 = lean_ctor_get(x_173, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_173);
x_606 = lean_ctor_get(x_604, 0);
lean_inc_ref(x_606);
lean_dec(x_604);
lean_inc(x_158);
x_607 = l_Lean_Environment_find_x3f(x_606, x_158, x_21);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; 
lean_free_object(x_165);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_608 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_609 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_608, x_3, x_4, x_5, x_605);
return x_609;
}
else
{
lean_object* x_610; lean_object* x_611; 
x_610 = lean_ctor_get(x_607, 0);
lean_inc(x_610);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 x_611 = x_607;
} else {
 lean_dec_ref(x_607);
 x_611 = lean_box(0);
}
switch (lean_obj_tag(x_610)) {
case 0:
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_611);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_612 = x_610;
} else {
 lean_dec_ref(x_610);
 x_612 = lean_box(0);
}
x_613 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_614 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_615 = 1;
x_616 = l_Lean_Name_toString(x_158, x_615);
if (lean_is_scalar(x_612)) {
 x_617 = lean_alloc_ctor(3, 1, 0);
} else {
 x_617 = x_612;
 lean_ctor_set_tag(x_617, 3);
}
lean_ctor_set(x_617, 0, x_616);
x_618 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_618, 0, x_614);
lean_ctor_set(x_618, 1, x_617);
x_619 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_619);
lean_ctor_set(x_165, 0, x_618);
x_620 = l_Lean_MessageData_ofFormat(x_165);
x_621 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_613, x_620, x_4, x_5, x_605);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_621;
}
case 2:
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_611);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_622 = x_610;
} else {
 lean_dec_ref(x_610);
 x_622 = lean_box(0);
}
x_623 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_624 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_625 = 1;
x_626 = l_Lean_Name_toString(x_158, x_625);
if (lean_is_scalar(x_622)) {
 x_627 = lean_alloc_ctor(3, 1, 0);
} else {
 x_627 = x_622;
 lean_ctor_set_tag(x_627, 3);
}
lean_ctor_set(x_627, 0, x_626);
x_628 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_628, 0, x_624);
lean_ctor_set(x_628, 1, x_627);
x_629 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_629);
lean_ctor_set(x_165, 0, x_628);
x_630 = l_Lean_MessageData_ofFormat(x_165);
x_631 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_623, x_630, x_4, x_5, x_605);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_631;
}
case 4:
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; uint8_t x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_611);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_632 = x_610;
} else {
 lean_dec_ref(x_610);
 x_632 = lean_box(0);
}
x_633 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_634 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_635 = 1;
x_636 = l_Lean_Name_toString(x_158, x_635);
if (lean_is_scalar(x_632)) {
 x_637 = lean_alloc_ctor(3, 1, 0);
} else {
 x_637 = x_632;
 lean_ctor_set_tag(x_637, 3);
}
lean_ctor_set(x_637, 0, x_636);
x_638 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_638, 0, x_634);
lean_ctor_set(x_638, 1, x_637);
x_639 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_639);
lean_ctor_set(x_165, 0, x_638);
x_640 = l_Lean_MessageData_ofFormat(x_165);
x_641 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_633, x_640, x_4, x_5, x_605);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_641;
}
case 5:
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_611);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_642 = x_610;
} else {
 lean_dec_ref(x_610);
 x_642 = lean_box(0);
}
x_643 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_644 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_645 = 1;
x_646 = l_Lean_Name_toString(x_158, x_645);
if (lean_is_scalar(x_642)) {
 x_647 = lean_alloc_ctor(3, 1, 0);
} else {
 x_647 = x_642;
 lean_ctor_set_tag(x_647, 3);
}
lean_ctor_set(x_647, 0, x_646);
x_648 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_648, 0, x_644);
lean_ctor_set(x_648, 1, x_647);
x_649 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_649);
lean_ctor_set(x_165, 0, x_648);
x_650 = l_Lean_MessageData_ofFormat(x_165);
x_651 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_643, x_650, x_4, x_5, x_605);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_651;
}
case 6:
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_free_object(x_165);
lean_inc(x_17);
lean_dec_ref(x_1);
x_652 = lean_ctor_get(x_610, 0);
lean_inc_ref(x_652);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_653 = x_610;
} else {
 lean_dec_ref(x_610);
 x_653 = lean_box(0);
}
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_652, 2);
lean_inc(x_655);
x_656 = lean_ctor_get(x_652, 3);
lean_inc(x_656);
lean_dec_ref(x_652);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_654);
x_657 = l_Lean_IR_hasTrivialStructure_x3f(x_654, x_4, x_5, x_605);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; 
lean_dec_ref(x_159);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec_ref(x_657);
lean_inc(x_5);
lean_inc_ref(x_4);
x_660 = l_Lean_IR_nameToIRType(x_654, x_4, x_5, x_659);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; uint8_t x_663; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
lean_dec_ref(x_660);
x_663 = l_Lean_IR_IRType_isScalar(x_661);
if (x_663 == 0)
{
lean_object* x_664; 
lean_dec(x_661);
lean_dec(x_655);
lean_dec(x_653);
lean_dec(x_611);
lean_inc(x_5);
lean_inc_ref(x_4);
x_664 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_662);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_690; lean_object* x_691; uint8_t x_692; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_667 = x_664;
} else {
 lean_dec_ref(x_664);
 x_667 = lean_box(0);
}
x_671 = lean_ctor_get(x_665, 0);
lean_inc_ref(x_671);
x_672 = lean_ctor_get(x_665, 1);
lean_inc_ref(x_672);
lean_dec(x_665);
x_673 = lean_array_get_size(x_163);
x_674 = l_Array_extract___redArg(x_163, x_656, x_673);
lean_dec(x_163);
x_690 = lean_array_get_size(x_674);
x_691 = lean_array_get_size(x_672);
x_692 = lean_nat_dec_eq(x_690, x_691);
lean_dec(x_690);
if (x_692 == 0)
{
lean_dec(x_691);
lean_dec_ref(x_674);
lean_dec_ref(x_672);
lean_dec_ref(x_671);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_670;
}
else
{
if (x_663 == 0)
{
lean_object* x_693; lean_object* x_694; uint8_t x_695; 
lean_dec(x_667);
x_693 = lean_unsigned_to_nat(0u);
x_694 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_695 = lean_nat_dec_lt(x_693, x_691);
if (x_695 == 0)
{
lean_dec(x_691);
x_675 = x_694;
x_676 = x_666;
goto block_689;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_696 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_697 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_672, x_696, x_674, x_691, x_694, x_693, x_666);
lean_dec(x_691);
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
lean_dec_ref(x_697);
x_675 = x_698;
x_676 = x_699;
goto block_689;
}
}
else
{
lean_dec(x_691);
lean_dec_ref(x_674);
lean_dec_ref(x_672);
lean_dec_ref(x_671);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_670;
}
}
block_670:
{
lean_object* x_668; lean_object* x_669; 
x_668 = lean_box(12);
if (lean_is_scalar(x_667)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_667;
}
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_666);
return x_669;
}
block_689:
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_677 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_676);
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_677, 1);
lean_inc(x_679);
if (lean_is_exclusive(x_677)) {
 lean_ctor_release(x_677, 0);
 lean_ctor_release(x_677, 1);
 x_680 = x_677;
} else {
 lean_dec_ref(x_677);
 x_680 = lean_box(0);
}
lean_inc(x_678);
x_681 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_671, x_672, x_674, x_678, x_3, x_4, x_5, x_679);
lean_dec_ref(x_674);
lean_dec_ref(x_672);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_684 = x_681;
} else {
 lean_dec_ref(x_681);
 x_684 = lean_box(0);
}
x_685 = l_Lean_IR_CtorInfo_type(x_671);
if (lean_is_scalar(x_680)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_680;
}
lean_ctor_set(x_686, 0, x_671);
lean_ctor_set(x_686, 1, x_675);
if (lean_is_scalar(x_20)) {
 x_687 = lean_alloc_ctor(0, 4, 0);
} else {
 x_687 = x_20;
}
lean_ctor_set(x_687, 0, x_678);
lean_ctor_set(x_687, 1, x_685);
lean_ctor_set(x_687, 2, x_686);
lean_ctor_set(x_687, 3, x_682);
if (lean_is_scalar(x_684)) {
 x_688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_688 = x_684;
}
lean_ctor_set(x_688, 0, x_687);
lean_ctor_set(x_688, 1, x_683);
return x_688;
}
else
{
lean_dec(x_680);
lean_dec(x_678);
lean_dec_ref(x_675);
lean_dec_ref(x_671);
lean_dec(x_20);
return x_681;
}
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_656);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_700 = lean_ctor_get(x_664, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_664, 1);
lean_inc(x_701);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_702 = x_664;
} else {
 lean_dec_ref(x_664);
 x_702 = lean_box(0);
}
if (lean_is_scalar(x_702)) {
 x_703 = lean_alloc_ctor(1, 2, 0);
} else {
 x_703 = x_702;
}
lean_ctor_set(x_703, 0, x_700);
lean_ctor_set(x_703, 1, x_701);
return x_703;
}
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_dec(x_656);
lean_dec(x_163);
lean_dec(x_158);
x_704 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_662);
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_704, 1);
lean_inc(x_706);
lean_dec_ref(x_704);
x_707 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_706);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_710 = x_707;
} else {
 lean_dec_ref(x_707);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_653)) {
 x_711 = lean_alloc_ctor(0, 1, 0);
} else {
 x_711 = x_653;
 lean_ctor_set_tag(x_711, 0);
}
lean_ctor_set(x_711, 0, x_655);
if (lean_is_scalar(x_611)) {
 x_712 = lean_alloc_ctor(11, 1, 0);
} else {
 x_712 = x_611;
 lean_ctor_set_tag(x_712, 11);
}
lean_ctor_set(x_712, 0, x_711);
if (lean_is_scalar(x_20)) {
 x_713 = lean_alloc_ctor(0, 4, 0);
} else {
 x_713 = x_20;
}
lean_ctor_set(x_713, 0, x_705);
lean_ctor_set(x_713, 1, x_661);
lean_ctor_set(x_713, 2, x_712);
lean_ctor_set(x_713, 3, x_708);
if (lean_is_scalar(x_710)) {
 x_714 = lean_alloc_ctor(0, 2, 0);
} else {
 x_714 = x_710;
}
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_709);
return x_714;
}
else
{
lean_dec(x_705);
lean_dec(x_661);
lean_dec(x_655);
lean_dec(x_653);
lean_dec(x_611);
lean_dec(x_20);
return x_707;
}
}
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_653);
lean_dec(x_611);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_715 = lean_ctor_get(x_660, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_660, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_717 = x_660;
} else {
 lean_dec_ref(x_660);
 x_717 = lean_box(0);
}
if (lean_is_scalar(x_717)) {
 x_718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_718 = x_717;
}
lean_ctor_set(x_718, 0, x_715);
lean_ctor_set(x_718, 1, x_716);
return x_718;
}
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_611);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_719 = lean_ctor_get(x_657, 1);
lean_inc(x_719);
lean_dec_ref(x_657);
x_720 = lean_ctor_get(x_658, 0);
lean_inc(x_720);
lean_dec_ref(x_658);
x_721 = lean_st_ref_take(x_3, x_719);
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec_ref(x_721);
x_724 = lean_ctor_get(x_720, 1);
lean_inc(x_724);
x_725 = lean_ctor_get(x_720, 2);
lean_inc(x_725);
lean_dec(x_720);
x_726 = lean_ctor_get(x_722, 0);
lean_inc_ref(x_726);
x_727 = lean_ctor_get(x_722, 1);
lean_inc_ref(x_727);
x_728 = lean_ctor_get(x_722, 2);
lean_inc(x_728);
x_729 = lean_ctor_get(x_722, 3);
lean_inc_ref(x_729);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 lean_ctor_release(x_722, 2);
 lean_ctor_release(x_722, 3);
 x_730 = x_722;
} else {
 lean_dec_ref(x_722);
 x_730 = lean_box(0);
}
x_731 = lean_box(0);
x_732 = lean_nat_add(x_724, x_725);
lean_dec(x_725);
lean_dec(x_724);
x_733 = lean_array_get(x_731, x_159, x_732);
lean_dec(x_732);
lean_dec_ref(x_159);
x_734 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_729, x_17, x_733);
if (lean_is_scalar(x_730)) {
 x_735 = lean_alloc_ctor(0, 4, 0);
} else {
 x_735 = x_730;
}
lean_ctor_set(x_735, 0, x_726);
lean_ctor_set(x_735, 1, x_727);
lean_ctor_set(x_735, 2, x_728);
lean_ctor_set(x_735, 3, x_734);
x_736 = lean_st_ref_set(x_3, x_735, x_723);
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
lean_dec_ref(x_736);
x_738 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_737);
return x_738;
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_611);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_739 = lean_ctor_get(x_657, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_657, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_741 = x_657;
} else {
 lean_dec_ref(x_657);
 x_741 = lean_box(0);
}
if (lean_is_scalar(x_741)) {
 x_742 = lean_alloc_ctor(1, 2, 0);
} else {
 x_742 = x_741;
}
lean_ctor_set(x_742, 0, x_739);
lean_ctor_set(x_742, 1, x_740);
return x_742;
}
}
case 7:
{
lean_object* x_743; lean_object* x_744; uint8_t x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_611);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_743 = x_610;
} else {
 lean_dec_ref(x_610);
 x_743 = lean_box(0);
}
x_744 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_745 = 1;
x_746 = l_Lean_Name_toString(x_158, x_745);
if (lean_is_scalar(x_743)) {
 x_747 = lean_alloc_ctor(3, 1, 0);
} else {
 x_747 = x_743;
 lean_ctor_set_tag(x_747, 3);
}
lean_ctor_set(x_747, 0, x_746);
x_748 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_748, 0, x_744);
lean_ctor_set(x_748, 1, x_747);
x_749 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_749);
lean_ctor_set(x_165, 0, x_748);
x_750 = l_Lean_MessageData_ofFormat(x_165);
x_751 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_750, x_4, x_5, x_605);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_751;
}
default: 
{
lean_object* x_752; 
lean_dec(x_611);
lean_dec(x_610);
lean_free_object(x_165);
lean_dec_ref(x_159);
lean_dec(x_20);
x_752 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_158, x_163, x_3, x_4, x_5, x_605);
return x_752;
}
}
}
}
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_free_object(x_165);
lean_dec_ref(x_159);
lean_dec(x_20);
x_753 = lean_ctor_get(x_171, 0);
lean_inc(x_753);
lean_dec_ref(x_171);
x_754 = lean_ctor_get(x_170, 1);
lean_inc(x_754);
lean_dec_ref(x_170);
x_755 = lean_ctor_get(x_753, 3);
lean_inc_ref(x_755);
lean_dec(x_753);
x_756 = lean_array_get_size(x_755);
lean_dec_ref(x_755);
x_757 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_158, x_756, x_163, x_3, x_4, x_5, x_754);
return x_757;
}
}
else
{
uint8_t x_758; 
lean_free_object(x_165);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_758 = !lean_is_exclusive(x_170);
if (x_758 == 0)
{
return x_170;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_759 = lean_ctor_get(x_170, 0);
x_760 = lean_ctor_get(x_170, 1);
lean_inc(x_760);
lean_inc(x_759);
lean_dec(x_170);
x_761 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
return x_761;
}
}
}
else
{
lean_object* x_762; lean_object* x_763; 
x_762 = lean_ctor_get(x_165, 1);
lean_inc(x_762);
lean_dec(x_165);
lean_inc(x_158);
x_763 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_158, x_5, x_762);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; 
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
if (lean_obj_tag(x_764) == 0)
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_765 = lean_ctor_get(x_763, 1);
lean_inc(x_765);
lean_dec_ref(x_763);
x_766 = lean_st_ref_get(x_5, x_765);
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
if (lean_is_exclusive(x_766)) {
 lean_ctor_release(x_766, 0);
 lean_ctor_release(x_766, 1);
 x_769 = x_766;
} else {
 lean_dec_ref(x_766);
 x_769 = lean_box(0);
}
x_770 = lean_ctor_get(x_767, 0);
lean_inc_ref(x_770);
lean_dec(x_767);
lean_inc(x_158);
x_771 = l_Lean_Environment_find_x3f(x_770, x_158, x_21);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; 
lean_dec(x_769);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_772 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_773 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_772, x_3, x_4, x_5, x_768);
return x_773;
}
else
{
lean_object* x_774; lean_object* x_775; 
x_774 = lean_ctor_get(x_771, 0);
lean_inc(x_774);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 x_775 = x_771;
} else {
 lean_dec_ref(x_771);
 x_775 = lean_box(0);
}
switch (lean_obj_tag(x_774)) {
case 0:
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; uint8_t x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_775);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_776 = x_774;
} else {
 lean_dec_ref(x_774);
 x_776 = lean_box(0);
}
x_777 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_778 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_779 = 1;
x_780 = l_Lean_Name_toString(x_158, x_779);
if (lean_is_scalar(x_776)) {
 x_781 = lean_alloc_ctor(3, 1, 0);
} else {
 x_781 = x_776;
 lean_ctor_set_tag(x_781, 3);
}
lean_ctor_set(x_781, 0, x_780);
if (lean_is_scalar(x_769)) {
 x_782 = lean_alloc_ctor(5, 2, 0);
} else {
 x_782 = x_769;
 lean_ctor_set_tag(x_782, 5);
}
lean_ctor_set(x_782, 0, x_778);
lean_ctor_set(x_782, 1, x_781);
x_783 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_784 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
x_785 = l_Lean_MessageData_ofFormat(x_784);
x_786 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_777, x_785, x_4, x_5, x_768);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_786;
}
case 2:
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; uint8_t x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
lean_dec(x_775);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_787 = x_774;
} else {
 lean_dec_ref(x_774);
 x_787 = lean_box(0);
}
x_788 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_789 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_790 = 1;
x_791 = l_Lean_Name_toString(x_158, x_790);
if (lean_is_scalar(x_787)) {
 x_792 = lean_alloc_ctor(3, 1, 0);
} else {
 x_792 = x_787;
 lean_ctor_set_tag(x_792, 3);
}
lean_ctor_set(x_792, 0, x_791);
if (lean_is_scalar(x_769)) {
 x_793 = lean_alloc_ctor(5, 2, 0);
} else {
 x_793 = x_769;
 lean_ctor_set_tag(x_793, 5);
}
lean_ctor_set(x_793, 0, x_789);
lean_ctor_set(x_793, 1, x_792);
x_794 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_795 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_795, 0, x_793);
lean_ctor_set(x_795, 1, x_794);
x_796 = l_Lean_MessageData_ofFormat(x_795);
x_797 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_788, x_796, x_4, x_5, x_768);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_797;
}
case 4:
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
lean_dec(x_775);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_798 = x_774;
} else {
 lean_dec_ref(x_774);
 x_798 = lean_box(0);
}
x_799 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_800 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_801 = 1;
x_802 = l_Lean_Name_toString(x_158, x_801);
if (lean_is_scalar(x_798)) {
 x_803 = lean_alloc_ctor(3, 1, 0);
} else {
 x_803 = x_798;
 lean_ctor_set_tag(x_803, 3);
}
lean_ctor_set(x_803, 0, x_802);
if (lean_is_scalar(x_769)) {
 x_804 = lean_alloc_ctor(5, 2, 0);
} else {
 x_804 = x_769;
 lean_ctor_set_tag(x_804, 5);
}
lean_ctor_set(x_804, 0, x_800);
lean_ctor_set(x_804, 1, x_803);
x_805 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_806 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
x_807 = l_Lean_MessageData_ofFormat(x_806);
x_808 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_799, x_807, x_4, x_5, x_768);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_808;
}
case 5:
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; uint8_t x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
lean_dec(x_775);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_809 = x_774;
} else {
 lean_dec_ref(x_774);
 x_809 = lean_box(0);
}
x_810 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_811 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_812 = 1;
x_813 = l_Lean_Name_toString(x_158, x_812);
if (lean_is_scalar(x_809)) {
 x_814 = lean_alloc_ctor(3, 1, 0);
} else {
 x_814 = x_809;
 lean_ctor_set_tag(x_814, 3);
}
lean_ctor_set(x_814, 0, x_813);
if (lean_is_scalar(x_769)) {
 x_815 = lean_alloc_ctor(5, 2, 0);
} else {
 x_815 = x_769;
 lean_ctor_set_tag(x_815, 5);
}
lean_ctor_set(x_815, 0, x_811);
lean_ctor_set(x_815, 1, x_814);
x_816 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_817 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set(x_817, 1, x_816);
x_818 = l_Lean_MessageData_ofFormat(x_817);
x_819 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_810, x_818, x_4, x_5, x_768);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_819;
}
case 6:
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
lean_dec(x_769);
lean_inc(x_17);
lean_dec_ref(x_1);
x_820 = lean_ctor_get(x_774, 0);
lean_inc_ref(x_820);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_821 = x_774;
} else {
 lean_dec_ref(x_774);
 x_821 = lean_box(0);
}
x_822 = lean_ctor_get(x_820, 1);
lean_inc(x_822);
x_823 = lean_ctor_get(x_820, 2);
lean_inc(x_823);
x_824 = lean_ctor_get(x_820, 3);
lean_inc(x_824);
lean_dec_ref(x_820);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_822);
x_825 = l_Lean_IR_hasTrivialStructure_x3f(x_822, x_4, x_5, x_768);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; 
lean_dec_ref(x_159);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec_ref(x_825);
lean_inc(x_5);
lean_inc_ref(x_4);
x_828 = l_Lean_IR_nameToIRType(x_822, x_4, x_5, x_827);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; uint8_t x_831; 
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
lean_dec_ref(x_828);
x_831 = l_Lean_IR_IRType_isScalar(x_829);
if (x_831 == 0)
{
lean_object* x_832; 
lean_dec(x_829);
lean_dec(x_823);
lean_dec(x_821);
lean_dec(x_775);
lean_inc(x_5);
lean_inc_ref(x_4);
x_832 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_830);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_858; lean_object* x_859; uint8_t x_860; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_835 = x_832;
} else {
 lean_dec_ref(x_832);
 x_835 = lean_box(0);
}
x_839 = lean_ctor_get(x_833, 0);
lean_inc_ref(x_839);
x_840 = lean_ctor_get(x_833, 1);
lean_inc_ref(x_840);
lean_dec(x_833);
x_841 = lean_array_get_size(x_163);
x_842 = l_Array_extract___redArg(x_163, x_824, x_841);
lean_dec(x_163);
x_858 = lean_array_get_size(x_842);
x_859 = lean_array_get_size(x_840);
x_860 = lean_nat_dec_eq(x_858, x_859);
lean_dec(x_858);
if (x_860 == 0)
{
lean_dec(x_859);
lean_dec_ref(x_842);
lean_dec_ref(x_840);
lean_dec_ref(x_839);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_838;
}
else
{
if (x_831 == 0)
{
lean_object* x_861; lean_object* x_862; uint8_t x_863; 
lean_dec(x_835);
x_861 = lean_unsigned_to_nat(0u);
x_862 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_863 = lean_nat_dec_lt(x_861, x_859);
if (x_863 == 0)
{
lean_dec(x_859);
x_843 = x_862;
x_844 = x_834;
goto block_857;
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_864 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_865 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_840, x_864, x_842, x_859, x_862, x_861, x_834);
lean_dec(x_859);
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec_ref(x_865);
x_843 = x_866;
x_844 = x_867;
goto block_857;
}
}
else
{
lean_dec(x_859);
lean_dec_ref(x_842);
lean_dec_ref(x_840);
lean_dec_ref(x_839);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_838;
}
}
block_838:
{
lean_object* x_836; lean_object* x_837; 
x_836 = lean_box(12);
if (lean_is_scalar(x_835)) {
 x_837 = lean_alloc_ctor(0, 2, 0);
} else {
 x_837 = x_835;
}
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_837, 1, x_834);
return x_837;
}
block_857:
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_845 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_844);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_848 = x_845;
} else {
 lean_dec_ref(x_845);
 x_848 = lean_box(0);
}
lean_inc(x_846);
x_849 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_839, x_840, x_842, x_846, x_3, x_4, x_5, x_847);
lean_dec_ref(x_842);
lean_dec_ref(x_840);
if (lean_obj_tag(x_849) == 0)
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_849, 1);
lean_inc(x_851);
if (lean_is_exclusive(x_849)) {
 lean_ctor_release(x_849, 0);
 lean_ctor_release(x_849, 1);
 x_852 = x_849;
} else {
 lean_dec_ref(x_849);
 x_852 = lean_box(0);
}
x_853 = l_Lean_IR_CtorInfo_type(x_839);
if (lean_is_scalar(x_848)) {
 x_854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_854 = x_848;
}
lean_ctor_set(x_854, 0, x_839);
lean_ctor_set(x_854, 1, x_843);
if (lean_is_scalar(x_20)) {
 x_855 = lean_alloc_ctor(0, 4, 0);
} else {
 x_855 = x_20;
}
lean_ctor_set(x_855, 0, x_846);
lean_ctor_set(x_855, 1, x_853);
lean_ctor_set(x_855, 2, x_854);
lean_ctor_set(x_855, 3, x_850);
if (lean_is_scalar(x_852)) {
 x_856 = lean_alloc_ctor(0, 2, 0);
} else {
 x_856 = x_852;
}
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_851);
return x_856;
}
else
{
lean_dec(x_848);
lean_dec(x_846);
lean_dec_ref(x_843);
lean_dec_ref(x_839);
lean_dec(x_20);
return x_849;
}
}
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_824);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_868 = lean_ctor_get(x_832, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_832, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_870 = x_832;
} else {
 lean_dec_ref(x_832);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(1, 2, 0);
} else {
 x_871 = x_870;
}
lean_ctor_set(x_871, 0, x_868);
lean_ctor_set(x_871, 1, x_869);
return x_871;
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_824);
lean_dec(x_163);
lean_dec(x_158);
x_872 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_830);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec_ref(x_872);
x_875 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_874);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_878 = x_875;
} else {
 lean_dec_ref(x_875);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_821)) {
 x_879 = lean_alloc_ctor(0, 1, 0);
} else {
 x_879 = x_821;
 lean_ctor_set_tag(x_879, 0);
}
lean_ctor_set(x_879, 0, x_823);
if (lean_is_scalar(x_775)) {
 x_880 = lean_alloc_ctor(11, 1, 0);
} else {
 x_880 = x_775;
 lean_ctor_set_tag(x_880, 11);
}
lean_ctor_set(x_880, 0, x_879);
if (lean_is_scalar(x_20)) {
 x_881 = lean_alloc_ctor(0, 4, 0);
} else {
 x_881 = x_20;
}
lean_ctor_set(x_881, 0, x_873);
lean_ctor_set(x_881, 1, x_829);
lean_ctor_set(x_881, 2, x_880);
lean_ctor_set(x_881, 3, x_876);
if (lean_is_scalar(x_878)) {
 x_882 = lean_alloc_ctor(0, 2, 0);
} else {
 x_882 = x_878;
}
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_877);
return x_882;
}
else
{
lean_dec(x_873);
lean_dec(x_829);
lean_dec(x_823);
lean_dec(x_821);
lean_dec(x_775);
lean_dec(x_20);
return x_875;
}
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_821);
lean_dec(x_775);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_883 = lean_ctor_get(x_828, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_828, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_885 = x_828;
} else {
 lean_dec_ref(x_828);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_775);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_887 = lean_ctor_get(x_825, 1);
lean_inc(x_887);
lean_dec_ref(x_825);
x_888 = lean_ctor_get(x_826, 0);
lean_inc(x_888);
lean_dec_ref(x_826);
x_889 = lean_st_ref_take(x_3, x_887);
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
lean_dec_ref(x_889);
x_892 = lean_ctor_get(x_888, 1);
lean_inc(x_892);
x_893 = lean_ctor_get(x_888, 2);
lean_inc(x_893);
lean_dec(x_888);
x_894 = lean_ctor_get(x_890, 0);
lean_inc_ref(x_894);
x_895 = lean_ctor_get(x_890, 1);
lean_inc_ref(x_895);
x_896 = lean_ctor_get(x_890, 2);
lean_inc(x_896);
x_897 = lean_ctor_get(x_890, 3);
lean_inc_ref(x_897);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 lean_ctor_release(x_890, 2);
 lean_ctor_release(x_890, 3);
 x_898 = x_890;
} else {
 lean_dec_ref(x_890);
 x_898 = lean_box(0);
}
x_899 = lean_box(0);
x_900 = lean_nat_add(x_892, x_893);
lean_dec(x_893);
lean_dec(x_892);
x_901 = lean_array_get(x_899, x_159, x_900);
lean_dec(x_900);
lean_dec_ref(x_159);
x_902 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerParam_spec__0___redArg(x_897, x_17, x_901);
if (lean_is_scalar(x_898)) {
 x_903 = lean_alloc_ctor(0, 4, 0);
} else {
 x_903 = x_898;
}
lean_ctor_set(x_903, 0, x_894);
lean_ctor_set(x_903, 1, x_895);
lean_ctor_set(x_903, 2, x_896);
lean_ctor_set(x_903, 3, x_902);
x_904 = lean_st_ref_set(x_3, x_903, x_891);
x_905 = lean_ctor_get(x_904, 1);
lean_inc(x_905);
lean_dec_ref(x_904);
x_906 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_905);
return x_906;
}
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_775);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_907 = lean_ctor_get(x_825, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_825, 1);
lean_inc(x_908);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_909 = x_825;
} else {
 lean_dec_ref(x_825);
 x_909 = lean_box(0);
}
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_907);
lean_ctor_set(x_910, 1, x_908);
return x_910;
}
}
case 7:
{
lean_object* x_911; lean_object* x_912; uint8_t x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
lean_dec(x_775);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_911 = x_774;
} else {
 lean_dec_ref(x_774);
 x_911 = lean_box(0);
}
x_912 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_913 = 1;
x_914 = l_Lean_Name_toString(x_158, x_913);
if (lean_is_scalar(x_911)) {
 x_915 = lean_alloc_ctor(3, 1, 0);
} else {
 x_915 = x_911;
 lean_ctor_set_tag(x_915, 3);
}
lean_ctor_set(x_915, 0, x_914);
if (lean_is_scalar(x_769)) {
 x_916 = lean_alloc_ctor(5, 2, 0);
} else {
 x_916 = x_769;
 lean_ctor_set_tag(x_916, 5);
}
lean_ctor_set(x_916, 0, x_912);
lean_ctor_set(x_916, 1, x_915);
x_917 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_918 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
x_919 = l_Lean_MessageData_ofFormat(x_918);
x_920 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_919, x_4, x_5, x_768);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_920;
}
default: 
{
lean_object* x_921; 
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_769);
lean_dec_ref(x_159);
lean_dec(x_20);
x_921 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_158, x_163, x_3, x_4, x_5, x_768);
return x_921;
}
}
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
lean_dec_ref(x_159);
lean_dec(x_20);
x_922 = lean_ctor_get(x_764, 0);
lean_inc(x_922);
lean_dec_ref(x_764);
x_923 = lean_ctor_get(x_763, 1);
lean_inc(x_923);
lean_dec_ref(x_763);
x_924 = lean_ctor_get(x_922, 3);
lean_inc_ref(x_924);
lean_dec(x_922);
x_925 = lean_array_get_size(x_924);
lean_dec_ref(x_924);
x_926 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_158, x_925, x_163, x_3, x_4, x_5, x_923);
return x_926;
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_927 = lean_ctor_get(x_763, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_763, 1);
lean_inc(x_928);
if (lean_is_exclusive(x_763)) {
 lean_ctor_release(x_763, 0);
 lean_ctor_release(x_763, 1);
 x_929 = x_763;
} else {
 lean_dec_ref(x_763);
 x_929 = lean_box(0);
}
if (lean_is_scalar(x_929)) {
 x_930 = lean_alloc_ctor(1, 2, 0);
} else {
 x_930 = x_929;
}
lean_ctor_set(x_930, 0, x_927);
lean_ctor_set(x_930, 1, x_928);
return x_930;
}
}
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
lean_dec_ref(x_159);
lean_dec(x_20);
x_931 = lean_ctor_get(x_165, 1);
lean_inc(x_931);
lean_dec_ref(x_165);
x_932 = lean_ctor_get(x_166, 0);
lean_inc(x_932);
lean_dec_ref(x_166);
x_933 = l_Lean_IR_Decl_params(x_932);
lean_dec(x_932);
x_934 = lean_array_get_size(x_933);
lean_dec_ref(x_933);
x_935 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_158, x_934, x_163, x_3, x_4, x_5, x_931);
return x_935;
}
}
default: 
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; 
lean_dec(x_20);
x_936 = lean_ctor_get(x_22, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_937);
lean_dec_ref(x_22);
x_938 = l_Lean_IR_ToIR_getFVarValue___redArg(x_936, x_3, x_16);
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
if (lean_obj_tag(x_939) == 0)
{
lean_object* x_940; lean_object* x_941; size_t x_942; size_t x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec_ref(x_938);
x_941 = lean_ctor_get(x_939, 0);
lean_inc(x_941);
lean_dec_ref(x_939);
x_942 = lean_array_size(x_937);
x_943 = 0;
x_944 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_942, x_943, x_937, x_3, x_940);
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
lean_dec_ref(x_944);
x_947 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(x_1, x_2, x_941, x_945, x_3, x_4, x_5, x_946);
return x_947;
}
else
{
lean_object* x_948; lean_object* x_949; 
lean_dec_ref(x_937);
x_948 = lean_ctor_get(x_938, 1);
lean_inc(x_948);
lean_dec_ref(x_938);
x_949 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_948);
return x_949;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_4);
x_15 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_15;
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
x_24 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_23, x_7, x_8, x_9, x_10);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
lean_inc(x_15);
lean_inc(x_21);
x_30 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_15);
lean_ctor_set(x_30, 3, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_17, 1);
x_33 = lean_ctor_get(x_17, 2);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_6, x_34);
lean_dec(x_6);
lean_inc(x_5);
x_36 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_35, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_2, 2);
x_40 = lean_ctor_get(x_2, 3);
x_41 = lean_nat_add(x_39, x_40);
lean_inc(x_33);
lean_inc(x_15);
lean_inc(x_32);
x_42 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_15);
lean_ctor_set(x_42, 4, x_33);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_36, 0, x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get(x_2, 3);
x_47 = lean_nat_add(x_45, x_46);
lean_inc(x_33);
lean_inc(x_15);
lean_inc(x_32);
x_48 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_32);
lean_ctor_set(x_48, 3, x_15);
lean_ctor_set(x_48, 4, x_33);
lean_ctor_set(x_48, 5, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
else
{
lean_dec(x_5);
return x_36;
}
}
default: 
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
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_6, x_53);
lean_dec(x_6);
x_6 = x_54;
goto _start;
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
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_18 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
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
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_17 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
return x_10;
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
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin, lean_io_mk_world());
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
