// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: public import Lean.Compiler.LCNF.Basic public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PhaseExt public import Lean.Compiler.IR.Basic public import Lean.Compiler.IR.CompilerM public import Lean.Compiler.IR.ToIRType public import Lean.CoreM public import Lean.Environment
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__8;
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
lean_object* l_Lean_IR_CtorInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__16;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_void_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__1;
lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__9;
static lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_void_elim___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getCtorLayout(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__12;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_1 = l_instMonadEIO(lean_box(0));
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
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_void_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_void_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_2 = lean_box(2);
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
x_3 = lean_unsigned_to_nat(312u);
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
lean_dec(x_24);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3___redArg(x_1, x_2, x_7);
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
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3___redArg(x_2, x_3, x_20);
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
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3_spec__3___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
x_20 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__1;
x_21 = lean_array_get_borrowed(x_20, x_1, x_6);
x_22 = lean_nat_dec_eq(x_6, x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = l_Lean_IR_ToIR_bindErased___redArg(x_23, x_7, x_8);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
x_10 = x_3;
x_11 = x_25;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_st_ref_take(x_7, x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_4, 2);
x_32 = lean_ctor_get(x_27, 3);
lean_inc(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
lean_inc(x_30);
x_34 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_32, x_30, x_33);
lean_ctor_set(x_27, 3, x_34);
x_35 = lean_st_ref_set(x_7, x_27, x_28);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_10 = x_3;
x_11 = x_36;
goto block_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_4, 2);
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
x_41 = lean_ctor_get(x_27, 2);
x_42 = lean_ctor_get(x_27, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
lean_inc(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
lean_inc(x_37);
x_44 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_42, x_37, x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_44);
x_46 = lean_st_ref_set(x_7, x_45, x_28);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_10 = x_3;
x_11 = x_47;
goto block_19;
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_14 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_9);
lean_inc(x_13);
lean_inc(x_5);
x_15 = lean_apply_2(x_14, x_5, x_13);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
x_6 = x_13;
x_8 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg(x_1, x_2, x_3, x_4, x_9, x_12, x_15, x_18);
return x_19;
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
x_3 = lean_unsigned_to_nat(154u);
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
x_3 = lean_unsigned_to_nat(146u);
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
x_3 = lean_unsigned_to_nat(133u);
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
x_3 = lean_unsigned_to_nat(135u);
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
x_3 = lean_unsigned_to_nat(136u);
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
x_3 = lean_unsigned_to_nat(134u);
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
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
x_150 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_149);
lean_inc(x_145);
x_151 = lean_apply_2(x_150, x_145, x_135);
x_152 = lean_unbox(x_151);
if (x_152 == 0)
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
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_box(0);
x_155 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg(x_138, x_141, x_154, x_62, x_145, x_135, x_2, x_127);
lean_dec_ref(x_62);
lean_dec(x_141);
lean_dec_ref(x_138);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec_ref(x_155);
x_1 = x_139;
x_5 = x_156;
goto _start;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_128);
lean_dec_ref(x_62);
x_158 = l_Lean_IR_ToIR_lowerCode___closed__12;
x_159 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_158, x_2, x_3, x_4, x_127);
return x_159;
}
}
}
}
else
{
uint8_t x_160; 
lean_dec_ref(x_62);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_66);
if (x_160 == 0)
{
return x_66;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_66, 0);
x_162 = lean_ctor_get(x_66, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_66);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
case 5:
{
uint8_t x_164; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_164 = !lean_is_exclusive(x_1);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = lean_ctor_get(x_1, 0);
x_166 = l_Lean_IR_ToIR_getFVarValue___redArg(x_165, x_2, x_5);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_166, 0);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_168);
lean_ctor_set(x_166, 0, x_1);
return x_166;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_166, 0);
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_166);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_1, 0);
lean_inc(x_172);
lean_dec(x_1);
x_173 = l_Lean_IR_ToIR_getFVarValue___redArg(x_172, x_2, x_5);
lean_dec(x_2);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_177, 0, x_174);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
return x_178;
}
}
default: 
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_179 = lean_box(12);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_5);
return x_180;
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
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_19; 
x_8 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
x_19 = lean_array_fget_borrowed(x_1, x_6);
switch (lean_obj_tag(x_19)) {
case 1:
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_2);
x_20 = lean_array_get_borrowed(x_2, x_3, x_6);
lean_inc(x_20);
x_21 = lean_array_push(x_5, x_20);
x_9 = x_21;
x_10 = x_7;
goto block_18;
}
case 2:
{
x_9 = x_5;
x_10 = x_7;
goto block_18;
}
case 3:
{
x_9 = x_5;
x_10 = x_7;
goto block_18;
}
default: 
{
x_9 = x_5;
x_10 = x_7;
goto block_18;
}
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_13 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_8);
lean_inc(x_12);
lean_inc(x_4);
x_14 = lean_apply_2(x_13, x_4, x_12);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
x_5 = x_9;
x_6 = x_12;
x_7 = x_10;
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
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_unsigned_to_nat(174u);
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
x_3 = lean_unsigned_to_nat(244u);
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
lean_dec(x_82);
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
x_120 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_119, x_17, x_58);
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
x_128 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_127, x_17, x_58);
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
x_149 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_146, x_17, x_148);
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
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
lean_dec(x_266);
x_304 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
x_305 = lean_unsigned_to_nat(0u);
x_306 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_307 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_304);
lean_inc(x_302);
x_308 = lean_apply_2(x_307, x_302, x_305);
x_309 = lean_unbox(x_308);
if (x_309 == 0)
{
lean_dec(x_302);
x_274 = x_306;
x_275 = x_265;
goto block_300;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_310 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_311 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_271, x_310, x_273, x_302, x_306, x_305, x_265);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec_ref(x_311);
x_274 = x_312;
x_275 = x_313;
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
uint8_t x_314; 
lean_dec(x_255);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_314 = !lean_is_exclusive(x_263);
if (x_314 == 0)
{
return x_263;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_263, 0);
x_316 = lean_ctor_get(x_263, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_263);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_255);
lean_dec(x_163);
lean_dec(x_158);
x_318 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_261);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec_ref(x_318);
x_321 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_320);
if (lean_obj_tag(x_321) == 0)
{
uint8_t x_322; 
x_322 = !lean_is_exclusive(x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_321, 0);
lean_ctor_set_tag(x_182, 0);
lean_ctor_set(x_182, 0, x_254);
lean_ctor_set_tag(x_178, 11);
if (lean_is_scalar(x_20)) {
 x_324 = lean_alloc_ctor(0, 4, 0);
} else {
 x_324 = x_20;
}
lean_ctor_set(x_324, 0, x_319);
lean_ctor_set(x_324, 1, x_260);
lean_ctor_set(x_324, 2, x_178);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set(x_321, 0, x_324);
return x_321;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_321, 0);
x_326 = lean_ctor_get(x_321, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_321);
lean_ctor_set_tag(x_182, 0);
lean_ctor_set(x_182, 0, x_254);
lean_ctor_set_tag(x_178, 11);
if (lean_is_scalar(x_20)) {
 x_327 = lean_alloc_ctor(0, 4, 0);
} else {
 x_327 = x_20;
}
lean_ctor_set(x_327, 0, x_319);
lean_ctor_set(x_327, 1, x_260);
lean_ctor_set(x_327, 2, x_178);
lean_ctor_set(x_327, 3, x_325);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
else
{
lean_dec(x_319);
lean_dec(x_260);
lean_dec(x_254);
lean_free_object(x_182);
lean_free_object(x_178);
lean_dec(x_20);
return x_321;
}
}
}
else
{
uint8_t x_329; 
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
x_329 = !lean_is_exclusive(x_259);
if (x_329 == 0)
{
return x_259;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_259, 0);
x_331 = lean_ctor_get(x_259, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_259);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_free_object(x_182);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_333 = lean_ctor_get(x_256, 1);
lean_inc(x_333);
lean_dec_ref(x_256);
x_334 = lean_ctor_get(x_257, 0);
lean_inc(x_334);
lean_dec_ref(x_257);
x_335 = lean_st_ref_take(x_3, x_333);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec_ref(x_335);
x_338 = lean_ctor_get(x_334, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_334, 2);
lean_inc(x_339);
lean_dec(x_334);
x_340 = !lean_is_exclusive(x_336);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_341 = lean_ctor_get(x_336, 3);
x_342 = lean_box(0);
x_343 = lean_nat_add(x_338, x_339);
lean_dec(x_339);
lean_dec(x_338);
x_344 = lean_array_get(x_342, x_159, x_343);
lean_dec(x_343);
lean_dec_ref(x_159);
x_345 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_341, x_17, x_344);
lean_ctor_set(x_336, 3, x_345);
x_346 = lean_st_ref_set(x_3, x_336, x_337);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec_ref(x_346);
x_348 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_347);
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_349 = lean_ctor_get(x_336, 0);
x_350 = lean_ctor_get(x_336, 1);
x_351 = lean_ctor_get(x_336, 2);
x_352 = lean_ctor_get(x_336, 3);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_336);
x_353 = lean_box(0);
x_354 = lean_nat_add(x_338, x_339);
lean_dec(x_339);
lean_dec(x_338);
x_355 = lean_array_get(x_353, x_159, x_354);
lean_dec(x_354);
lean_dec_ref(x_159);
x_356 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_352, x_17, x_355);
x_357 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_357, 0, x_349);
lean_ctor_set(x_357, 1, x_350);
lean_ctor_set(x_357, 2, x_351);
lean_ctor_set(x_357, 3, x_356);
x_358 = lean_st_ref_set(x_3, x_357, x_337);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
lean_dec_ref(x_358);
x_360 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_359);
return x_360;
}
}
}
else
{
uint8_t x_361; 
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
x_361 = !lean_is_exclusive(x_256);
if (x_361 == 0)
{
return x_256;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_256, 0);
x_363 = lean_ctor_get(x_256, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_256);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_365 = lean_ctor_get(x_182, 0);
lean_inc(x_365);
lean_dec(x_182);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_365, 3);
lean_inc(x_368);
lean_dec_ref(x_365);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_366);
x_369 = l_Lean_IR_hasTrivialStructure_x3f(x_366, x_4, x_5, x_176);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; 
lean_dec_ref(x_159);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec_ref(x_369);
lean_inc(x_5);
lean_inc_ref(x_4);
x_372 = l_Lean_IR_nameToIRType(x_366, x_4, x_5, x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec_ref(x_372);
x_375 = l_Lean_IR_IRType_isScalar(x_373);
if (x_375 == 0)
{
lean_object* x_376; 
lean_dec(x_373);
lean_dec(x_367);
lean_free_object(x_178);
lean_inc(x_5);
lean_inc_ref(x_4);
x_376 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_374);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_379 = x_376;
} else {
 lean_dec_ref(x_376);
 x_379 = lean_box(0);
}
x_383 = lean_ctor_get(x_377, 0);
lean_inc_ref(x_383);
x_384 = lean_ctor_get(x_377, 1);
lean_inc_ref(x_384);
lean_dec(x_377);
x_385 = lean_array_get_size(x_163);
x_386 = l_Array_extract___redArg(x_163, x_368, x_385);
lean_dec(x_163);
x_402 = lean_array_get_size(x_386);
x_403 = lean_array_get_size(x_384);
x_404 = lean_nat_dec_eq(x_402, x_403);
lean_dec(x_402);
if (x_404 == 0)
{
lean_dec(x_403);
lean_dec_ref(x_386);
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_382;
}
else
{
if (x_375 == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
lean_dec(x_379);
x_405 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
x_406 = lean_unsigned_to_nat(0u);
x_407 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_408 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_405);
lean_inc(x_403);
x_409 = lean_apply_2(x_408, x_403, x_406);
x_410 = lean_unbox(x_409);
if (x_410 == 0)
{
lean_dec(x_403);
x_387 = x_407;
x_388 = x_378;
goto block_401;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_411 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_412 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_384, x_411, x_386, x_403, x_407, x_406, x_378);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec_ref(x_412);
x_387 = x_413;
x_388 = x_414;
goto block_401;
}
}
else
{
lean_dec(x_403);
lean_dec_ref(x_386);
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_382;
}
}
block_382:
{
lean_object* x_380; lean_object* x_381; 
x_380 = lean_box(12);
if (lean_is_scalar(x_379)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_379;
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_378);
return x_381;
}
block_401:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_389 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_388);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
lean_inc(x_390);
x_393 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_383, x_384, x_386, x_390, x_3, x_4, x_5, x_391);
lean_dec_ref(x_386);
lean_dec_ref(x_384);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_396 = x_393;
} else {
 lean_dec_ref(x_393);
 x_396 = lean_box(0);
}
x_397 = l_Lean_IR_CtorInfo_type(x_383);
if (lean_is_scalar(x_392)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_392;
}
lean_ctor_set(x_398, 0, x_383);
lean_ctor_set(x_398, 1, x_387);
if (lean_is_scalar(x_20)) {
 x_399 = lean_alloc_ctor(0, 4, 0);
} else {
 x_399 = x_20;
}
lean_ctor_set(x_399, 0, x_390);
lean_ctor_set(x_399, 1, x_397);
lean_ctor_set(x_399, 2, x_398);
lean_ctor_set(x_399, 3, x_394);
if (lean_is_scalar(x_396)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_396;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_395);
return x_400;
}
else
{
lean_dec(x_392);
lean_dec(x_390);
lean_dec_ref(x_387);
lean_dec_ref(x_383);
lean_dec(x_20);
return x_393;
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_368);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_415 = lean_ctor_get(x_376, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_376, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_417 = x_376;
} else {
 lean_dec_ref(x_376);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_368);
lean_dec(x_163);
lean_dec(x_158);
x_419 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_374);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec_ref(x_419);
x_422 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_425 = x_422;
} else {
 lean_dec_ref(x_422);
 x_425 = lean_box(0);
}
x_426 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_426, 0, x_367);
lean_ctor_set_tag(x_178, 11);
lean_ctor_set(x_178, 0, x_426);
if (lean_is_scalar(x_20)) {
 x_427 = lean_alloc_ctor(0, 4, 0);
} else {
 x_427 = x_20;
}
lean_ctor_set(x_427, 0, x_420);
lean_ctor_set(x_427, 1, x_373);
lean_ctor_set(x_427, 2, x_178);
lean_ctor_set(x_427, 3, x_423);
if (lean_is_scalar(x_425)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_425;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_424);
return x_428;
}
else
{
lean_dec(x_420);
lean_dec(x_373);
lean_dec(x_367);
lean_free_object(x_178);
lean_dec(x_20);
return x_422;
}
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_368);
lean_dec(x_367);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_429 = lean_ctor_get(x_372, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_372, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_431 = x_372;
} else {
 lean_dec_ref(x_372);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_free_object(x_178);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_433 = lean_ctor_get(x_369, 1);
lean_inc(x_433);
lean_dec_ref(x_369);
x_434 = lean_ctor_get(x_370, 0);
lean_inc(x_434);
lean_dec_ref(x_370);
x_435 = lean_st_ref_take(x_3, x_433);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec_ref(x_435);
x_438 = lean_ctor_get(x_434, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_434, 2);
lean_inc(x_439);
lean_dec(x_434);
x_440 = lean_ctor_get(x_436, 0);
lean_inc_ref(x_440);
x_441 = lean_ctor_get(x_436, 1);
lean_inc_ref(x_441);
x_442 = lean_ctor_get(x_436, 2);
lean_inc(x_442);
x_443 = lean_ctor_get(x_436, 3);
lean_inc_ref(x_443);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 lean_ctor_release(x_436, 2);
 lean_ctor_release(x_436, 3);
 x_444 = x_436;
} else {
 lean_dec_ref(x_436);
 x_444 = lean_box(0);
}
x_445 = lean_box(0);
x_446 = lean_nat_add(x_438, x_439);
lean_dec(x_439);
lean_dec(x_438);
x_447 = lean_array_get(x_445, x_159, x_446);
lean_dec(x_446);
lean_dec_ref(x_159);
x_448 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_443, x_17, x_447);
if (lean_is_scalar(x_444)) {
 x_449 = lean_alloc_ctor(0, 4, 0);
} else {
 x_449 = x_444;
}
lean_ctor_set(x_449, 0, x_440);
lean_ctor_set(x_449, 1, x_441);
lean_ctor_set(x_449, 2, x_442);
lean_ctor_set(x_449, 3, x_448);
x_450 = lean_st_ref_set(x_3, x_449, x_437);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec_ref(x_450);
x_452 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_451);
return x_452;
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_366);
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
x_453 = lean_ctor_get(x_369, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_369, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_455 = x_369;
} else {
 lean_dec_ref(x_369);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 2, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_453);
lean_ctor_set(x_456, 1, x_454);
return x_456;
}
}
}
case 7:
{
uint8_t x_457; 
lean_free_object(x_178);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_457 = !lean_is_exclusive(x_182);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_458 = lean_ctor_get(x_182, 0);
lean_dec(x_458);
x_459 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_460 = 1;
x_461 = l_Lean_Name_toString(x_158, x_460);
lean_ctor_set_tag(x_182, 3);
lean_ctor_set(x_182, 0, x_461);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_182);
lean_ctor_set(x_173, 0, x_459);
x_462 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_462);
lean_ctor_set(x_165, 0, x_173);
x_463 = l_Lean_MessageData_ofFormat(x_165);
x_464 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_463, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_464;
}
else
{
lean_object* x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_182);
x_465 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_466 = 1;
x_467 = l_Lean_Name_toString(x_158, x_466);
x_468 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_468);
lean_ctor_set(x_173, 0, x_465);
x_469 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_469);
lean_ctor_set(x_165, 0, x_173);
x_470 = l_Lean_MessageData_ofFormat(x_165);
x_471 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_470, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_471;
}
}
default: 
{
lean_object* x_472; 
lean_free_object(x_178);
lean_dec(x_182);
lean_free_object(x_173);
lean_free_object(x_165);
lean_dec_ref(x_159);
lean_dec(x_20);
x_472 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_158, x_163, x_3, x_4, x_5, x_176);
return x_472;
}
}
}
else
{
lean_object* x_473; 
x_473 = lean_ctor_get(x_178, 0);
lean_inc(x_473);
lean_dec(x_178);
switch (lean_obj_tag(x_473)) {
case 0:
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_474 = x_473;
} else {
 lean_dec_ref(x_473);
 x_474 = lean_box(0);
}
x_475 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_476 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_477 = 1;
x_478 = l_Lean_Name_toString(x_158, x_477);
if (lean_is_scalar(x_474)) {
 x_479 = lean_alloc_ctor(3, 1, 0);
} else {
 x_479 = x_474;
 lean_ctor_set_tag(x_479, 3);
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_479);
lean_ctor_set(x_173, 0, x_476);
x_480 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_480);
lean_ctor_set(x_165, 0, x_173);
x_481 = l_Lean_MessageData_ofFormat(x_165);
x_482 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_475, x_481, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_482;
}
case 2:
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_483 = x_473;
} else {
 lean_dec_ref(x_473);
 x_483 = lean_box(0);
}
x_484 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_485 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_486 = 1;
x_487 = l_Lean_Name_toString(x_158, x_486);
if (lean_is_scalar(x_483)) {
 x_488 = lean_alloc_ctor(3, 1, 0);
} else {
 x_488 = x_483;
 lean_ctor_set_tag(x_488, 3);
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_488);
lean_ctor_set(x_173, 0, x_485);
x_489 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_489);
lean_ctor_set(x_165, 0, x_173);
x_490 = l_Lean_MessageData_ofFormat(x_165);
x_491 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_484, x_490, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_491;
}
case 4:
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_492 = x_473;
} else {
 lean_dec_ref(x_473);
 x_492 = lean_box(0);
}
x_493 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_494 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_495 = 1;
x_496 = l_Lean_Name_toString(x_158, x_495);
if (lean_is_scalar(x_492)) {
 x_497 = lean_alloc_ctor(3, 1, 0);
} else {
 x_497 = x_492;
 lean_ctor_set_tag(x_497, 3);
}
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_497);
lean_ctor_set(x_173, 0, x_494);
x_498 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_498);
lean_ctor_set(x_165, 0, x_173);
x_499 = l_Lean_MessageData_ofFormat(x_165);
x_500 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_493, x_499, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_500;
}
case 5:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_501 = x_473;
} else {
 lean_dec_ref(x_473);
 x_501 = lean_box(0);
}
x_502 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_503 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_504 = 1;
x_505 = l_Lean_Name_toString(x_158, x_504);
if (lean_is_scalar(x_501)) {
 x_506 = lean_alloc_ctor(3, 1, 0);
} else {
 x_506 = x_501;
 lean_ctor_set_tag(x_506, 3);
}
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_506);
lean_ctor_set(x_173, 0, x_503);
x_507 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_507);
lean_ctor_set(x_165, 0, x_173);
x_508 = l_Lean_MessageData_ofFormat(x_165);
x_509 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_502, x_508, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_509;
}
case 6:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_free_object(x_173);
lean_free_object(x_165);
lean_inc(x_17);
lean_dec_ref(x_1);
x_510 = lean_ctor_get(x_473, 0);
lean_inc_ref(x_510);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_511 = x_473;
} else {
 lean_dec_ref(x_473);
 x_511 = lean_box(0);
}
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
x_513 = lean_ctor_get(x_510, 2);
lean_inc(x_513);
x_514 = lean_ctor_get(x_510, 3);
lean_inc(x_514);
lean_dec_ref(x_510);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_512);
x_515 = l_Lean_IR_hasTrivialStructure_x3f(x_512, x_4, x_5, x_176);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; 
lean_dec_ref(x_159);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec_ref(x_515);
lean_inc(x_5);
lean_inc_ref(x_4);
x_518 = l_Lean_IR_nameToIRType(x_512, x_4, x_5, x_517);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec_ref(x_518);
x_521 = l_Lean_IR_IRType_isScalar(x_519);
if (x_521 == 0)
{
lean_object* x_522; 
lean_dec(x_519);
lean_dec(x_513);
lean_dec(x_511);
lean_inc(x_5);
lean_inc_ref(x_4);
x_522 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_520);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_548; lean_object* x_549; uint8_t x_550; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_525 = x_522;
} else {
 lean_dec_ref(x_522);
 x_525 = lean_box(0);
}
x_529 = lean_ctor_get(x_523, 0);
lean_inc_ref(x_529);
x_530 = lean_ctor_get(x_523, 1);
lean_inc_ref(x_530);
lean_dec(x_523);
x_531 = lean_array_get_size(x_163);
x_532 = l_Array_extract___redArg(x_163, x_514, x_531);
lean_dec(x_163);
x_548 = lean_array_get_size(x_532);
x_549 = lean_array_get_size(x_530);
x_550 = lean_nat_dec_eq(x_548, x_549);
lean_dec(x_548);
if (x_550 == 0)
{
lean_dec(x_549);
lean_dec_ref(x_532);
lean_dec_ref(x_530);
lean_dec_ref(x_529);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_528;
}
else
{
if (x_521 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; 
lean_dec(x_525);
x_551 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
x_552 = lean_unsigned_to_nat(0u);
x_553 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_554 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_551);
lean_inc(x_549);
x_555 = lean_apply_2(x_554, x_549, x_552);
x_556 = lean_unbox(x_555);
if (x_556 == 0)
{
lean_dec(x_549);
x_533 = x_553;
x_534 = x_524;
goto block_547;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_557 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_558 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_530, x_557, x_532, x_549, x_553, x_552, x_524);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec_ref(x_558);
x_533 = x_559;
x_534 = x_560;
goto block_547;
}
}
else
{
lean_dec(x_549);
lean_dec_ref(x_532);
lean_dec_ref(x_530);
lean_dec_ref(x_529);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_528;
}
}
block_528:
{
lean_object* x_526; lean_object* x_527; 
x_526 = lean_box(12);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_524);
return x_527;
}
block_547:
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_535 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_534);
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_538 = x_535;
} else {
 lean_dec_ref(x_535);
 x_538 = lean_box(0);
}
lean_inc(x_536);
x_539 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_529, x_530, x_532, x_536, x_3, x_4, x_5, x_537);
lean_dec_ref(x_532);
lean_dec_ref(x_530);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_542 = x_539;
} else {
 lean_dec_ref(x_539);
 x_542 = lean_box(0);
}
x_543 = l_Lean_IR_CtorInfo_type(x_529);
if (lean_is_scalar(x_538)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_538;
}
lean_ctor_set(x_544, 0, x_529);
lean_ctor_set(x_544, 1, x_533);
if (lean_is_scalar(x_20)) {
 x_545 = lean_alloc_ctor(0, 4, 0);
} else {
 x_545 = x_20;
}
lean_ctor_set(x_545, 0, x_536);
lean_ctor_set(x_545, 1, x_543);
lean_ctor_set(x_545, 2, x_544);
lean_ctor_set(x_545, 3, x_540);
if (lean_is_scalar(x_542)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_542;
}
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_541);
return x_546;
}
else
{
lean_dec(x_538);
lean_dec(x_536);
lean_dec_ref(x_533);
lean_dec_ref(x_529);
lean_dec(x_20);
return x_539;
}
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_514);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_561 = lean_ctor_get(x_522, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_522, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_563 = x_522;
} else {
 lean_dec_ref(x_522);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_561);
lean_ctor_set(x_564, 1, x_562);
return x_564;
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_514);
lean_dec(x_163);
lean_dec(x_158);
x_565 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_520);
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
lean_dec_ref(x_565);
x_568 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_567);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_571 = x_568;
} else {
 lean_dec_ref(x_568);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_572 = lean_alloc_ctor(0, 1, 0);
} else {
 x_572 = x_511;
 lean_ctor_set_tag(x_572, 0);
}
lean_ctor_set(x_572, 0, x_513);
x_573 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_573, 0, x_572);
if (lean_is_scalar(x_20)) {
 x_574 = lean_alloc_ctor(0, 4, 0);
} else {
 x_574 = x_20;
}
lean_ctor_set(x_574, 0, x_566);
lean_ctor_set(x_574, 1, x_519);
lean_ctor_set(x_574, 2, x_573);
lean_ctor_set(x_574, 3, x_569);
if (lean_is_scalar(x_571)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_571;
}
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_570);
return x_575;
}
else
{
lean_dec(x_566);
lean_dec(x_519);
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_20);
return x_568;
}
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_576 = lean_ctor_get(x_518, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_518, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_578 = x_518;
} else {
 lean_dec_ref(x_518);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_577);
return x_579;
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_580 = lean_ctor_get(x_515, 1);
lean_inc(x_580);
lean_dec_ref(x_515);
x_581 = lean_ctor_get(x_516, 0);
lean_inc(x_581);
lean_dec_ref(x_516);
x_582 = lean_st_ref_take(x_3, x_580);
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec_ref(x_582);
x_585 = lean_ctor_get(x_581, 1);
lean_inc(x_585);
x_586 = lean_ctor_get(x_581, 2);
lean_inc(x_586);
lean_dec(x_581);
x_587 = lean_ctor_get(x_583, 0);
lean_inc_ref(x_587);
x_588 = lean_ctor_get(x_583, 1);
lean_inc_ref(x_588);
x_589 = lean_ctor_get(x_583, 2);
lean_inc(x_589);
x_590 = lean_ctor_get(x_583, 3);
lean_inc_ref(x_590);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 lean_ctor_release(x_583, 2);
 lean_ctor_release(x_583, 3);
 x_591 = x_583;
} else {
 lean_dec_ref(x_583);
 x_591 = lean_box(0);
}
x_592 = lean_box(0);
x_593 = lean_nat_add(x_585, x_586);
lean_dec(x_586);
lean_dec(x_585);
x_594 = lean_array_get(x_592, x_159, x_593);
lean_dec(x_593);
lean_dec_ref(x_159);
x_595 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_590, x_17, x_594);
if (lean_is_scalar(x_591)) {
 x_596 = lean_alloc_ctor(0, 4, 0);
} else {
 x_596 = x_591;
}
lean_ctor_set(x_596, 0, x_587);
lean_ctor_set(x_596, 1, x_588);
lean_ctor_set(x_596, 2, x_589);
lean_ctor_set(x_596, 3, x_595);
x_597 = lean_st_ref_set(x_3, x_596, x_584);
x_598 = lean_ctor_get(x_597, 1);
lean_inc(x_598);
lean_dec_ref(x_597);
x_599 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_598);
return x_599;
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_600 = lean_ctor_get(x_515, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_515, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 x_602 = x_515;
} else {
 lean_dec_ref(x_515);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_600);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
}
case 7:
{
lean_object* x_604; lean_object* x_605; uint8_t x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_604 = x_473;
} else {
 lean_dec_ref(x_473);
 x_604 = lean_box(0);
}
x_605 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_606 = 1;
x_607 = l_Lean_Name_toString(x_158, x_606);
if (lean_is_scalar(x_604)) {
 x_608 = lean_alloc_ctor(3, 1, 0);
} else {
 x_608 = x_604;
 lean_ctor_set_tag(x_608, 3);
}
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set_tag(x_173, 5);
lean_ctor_set(x_173, 1, x_608);
lean_ctor_set(x_173, 0, x_605);
x_609 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_609);
lean_ctor_set(x_165, 0, x_173);
x_610 = l_Lean_MessageData_ofFormat(x_165);
x_611 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_610, x_4, x_5, x_176);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_611;
}
default: 
{
lean_object* x_612; 
lean_dec(x_473);
lean_free_object(x_173);
lean_free_object(x_165);
lean_dec_ref(x_159);
lean_dec(x_20);
x_612 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_158, x_163, x_3, x_4, x_5, x_176);
return x_612;
}
}
}
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_613 = lean_ctor_get(x_173, 0);
x_614 = lean_ctor_get(x_173, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_173);
x_615 = lean_ctor_get(x_613, 0);
lean_inc_ref(x_615);
lean_dec(x_613);
lean_inc(x_158);
x_616 = l_Lean_Environment_find_x3f(x_615, x_158, x_21);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; 
lean_free_object(x_165);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_617 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_618 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_617, x_3, x_4, x_5, x_614);
return x_618;
}
else
{
lean_object* x_619; lean_object* x_620; 
x_619 = lean_ctor_get(x_616, 0);
lean_inc(x_619);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 x_620 = x_616;
} else {
 lean_dec_ref(x_616);
 x_620 = lean_box(0);
}
switch (lean_obj_tag(x_619)) {
case 0:
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_620);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 x_621 = x_619;
} else {
 lean_dec_ref(x_619);
 x_621 = lean_box(0);
}
x_622 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_623 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_624 = 1;
x_625 = l_Lean_Name_toString(x_158, x_624);
if (lean_is_scalar(x_621)) {
 x_626 = lean_alloc_ctor(3, 1, 0);
} else {
 x_626 = x_621;
 lean_ctor_set_tag(x_626, 3);
}
lean_ctor_set(x_626, 0, x_625);
x_627 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_627, 0, x_623);
lean_ctor_set(x_627, 1, x_626);
x_628 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_628);
lean_ctor_set(x_165, 0, x_627);
x_629 = l_Lean_MessageData_ofFormat(x_165);
x_630 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_622, x_629, x_4, x_5, x_614);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_630;
}
case 2:
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_620);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 x_631 = x_619;
} else {
 lean_dec_ref(x_619);
 x_631 = lean_box(0);
}
x_632 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_633 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_634 = 1;
x_635 = l_Lean_Name_toString(x_158, x_634);
if (lean_is_scalar(x_631)) {
 x_636 = lean_alloc_ctor(3, 1, 0);
} else {
 x_636 = x_631;
 lean_ctor_set_tag(x_636, 3);
}
lean_ctor_set(x_636, 0, x_635);
x_637 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_637, 0, x_633);
lean_ctor_set(x_637, 1, x_636);
x_638 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_638);
lean_ctor_set(x_165, 0, x_637);
x_639 = l_Lean_MessageData_ofFormat(x_165);
x_640 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_632, x_639, x_4, x_5, x_614);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_640;
}
case 4:
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_620);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 x_641 = x_619;
} else {
 lean_dec_ref(x_619);
 x_641 = lean_box(0);
}
x_642 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_643 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_644 = 1;
x_645 = l_Lean_Name_toString(x_158, x_644);
if (lean_is_scalar(x_641)) {
 x_646 = lean_alloc_ctor(3, 1, 0);
} else {
 x_646 = x_641;
 lean_ctor_set_tag(x_646, 3);
}
lean_ctor_set(x_646, 0, x_645);
x_647 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_647, 0, x_643);
lean_ctor_set(x_647, 1, x_646);
x_648 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_648);
lean_ctor_set(x_165, 0, x_647);
x_649 = l_Lean_MessageData_ofFormat(x_165);
x_650 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_642, x_649, x_4, x_5, x_614);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_650;
}
case 5:
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_620);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 x_651 = x_619;
} else {
 lean_dec_ref(x_619);
 x_651 = lean_box(0);
}
x_652 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_653 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_654 = 1;
x_655 = l_Lean_Name_toString(x_158, x_654);
if (lean_is_scalar(x_651)) {
 x_656 = lean_alloc_ctor(3, 1, 0);
} else {
 x_656 = x_651;
 lean_ctor_set_tag(x_656, 3);
}
lean_ctor_set(x_656, 0, x_655);
x_657 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_657, 0, x_653);
lean_ctor_set(x_657, 1, x_656);
x_658 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_658);
lean_ctor_set(x_165, 0, x_657);
x_659 = l_Lean_MessageData_ofFormat(x_165);
x_660 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_652, x_659, x_4, x_5, x_614);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_660;
}
case 6:
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_free_object(x_165);
lean_inc(x_17);
lean_dec_ref(x_1);
x_661 = lean_ctor_get(x_619, 0);
lean_inc_ref(x_661);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 x_662 = x_619;
} else {
 lean_dec_ref(x_619);
 x_662 = lean_box(0);
}
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
x_664 = lean_ctor_get(x_661, 2);
lean_inc(x_664);
x_665 = lean_ctor_get(x_661, 3);
lean_inc(x_665);
lean_dec_ref(x_661);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_663);
x_666 = l_Lean_IR_hasTrivialStructure_x3f(x_663, x_4, x_5, x_614);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; 
lean_dec_ref(x_159);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
lean_dec_ref(x_666);
lean_inc(x_5);
lean_inc_ref(x_4);
x_669 = l_Lean_IR_nameToIRType(x_663, x_4, x_5, x_668);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; uint8_t x_672; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec_ref(x_669);
x_672 = l_Lean_IR_IRType_isScalar(x_670);
if (x_672 == 0)
{
lean_object* x_673; 
lean_dec(x_670);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_620);
lean_inc(x_5);
lean_inc_ref(x_4);
x_673 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_671);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_699; lean_object* x_700; uint8_t x_701; 
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_676 = x_673;
} else {
 lean_dec_ref(x_673);
 x_676 = lean_box(0);
}
x_680 = lean_ctor_get(x_674, 0);
lean_inc_ref(x_680);
x_681 = lean_ctor_get(x_674, 1);
lean_inc_ref(x_681);
lean_dec(x_674);
x_682 = lean_array_get_size(x_163);
x_683 = l_Array_extract___redArg(x_163, x_665, x_682);
lean_dec(x_163);
x_699 = lean_array_get_size(x_683);
x_700 = lean_array_get_size(x_681);
x_701 = lean_nat_dec_eq(x_699, x_700);
lean_dec(x_699);
if (x_701 == 0)
{
lean_dec(x_700);
lean_dec_ref(x_683);
lean_dec_ref(x_681);
lean_dec_ref(x_680);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_679;
}
else
{
if (x_672 == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; 
lean_dec(x_676);
x_702 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
x_703 = lean_unsigned_to_nat(0u);
x_704 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_705 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_702);
lean_inc(x_700);
x_706 = lean_apply_2(x_705, x_700, x_703);
x_707 = lean_unbox(x_706);
if (x_707 == 0)
{
lean_dec(x_700);
x_684 = x_704;
x_685 = x_675;
goto block_698;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_708 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_709 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_681, x_708, x_683, x_700, x_704, x_703, x_675);
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec_ref(x_709);
x_684 = x_710;
x_685 = x_711;
goto block_698;
}
}
else
{
lean_dec(x_700);
lean_dec_ref(x_683);
lean_dec_ref(x_681);
lean_dec_ref(x_680);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_679;
}
}
block_679:
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_box(12);
if (lean_is_scalar(x_676)) {
 x_678 = lean_alloc_ctor(0, 2, 0);
} else {
 x_678 = x_676;
}
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_675);
return x_678;
}
block_698:
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_686 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_685);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_689 = x_686;
} else {
 lean_dec_ref(x_686);
 x_689 = lean_box(0);
}
lean_inc(x_687);
x_690 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_680, x_681, x_683, x_687, x_3, x_4, x_5, x_688);
lean_dec_ref(x_683);
lean_dec_ref(x_681);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_693 = x_690;
} else {
 lean_dec_ref(x_690);
 x_693 = lean_box(0);
}
x_694 = l_Lean_IR_CtorInfo_type(x_680);
if (lean_is_scalar(x_689)) {
 x_695 = lean_alloc_ctor(0, 2, 0);
} else {
 x_695 = x_689;
}
lean_ctor_set(x_695, 0, x_680);
lean_ctor_set(x_695, 1, x_684);
if (lean_is_scalar(x_20)) {
 x_696 = lean_alloc_ctor(0, 4, 0);
} else {
 x_696 = x_20;
}
lean_ctor_set(x_696, 0, x_687);
lean_ctor_set(x_696, 1, x_694);
lean_ctor_set(x_696, 2, x_695);
lean_ctor_set(x_696, 3, x_691);
if (lean_is_scalar(x_693)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_693;
}
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_692);
return x_697;
}
else
{
lean_dec(x_689);
lean_dec(x_687);
lean_dec_ref(x_684);
lean_dec_ref(x_680);
lean_dec(x_20);
return x_690;
}
}
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
lean_dec(x_665);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_712 = lean_ctor_get(x_673, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_673, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_714 = x_673;
} else {
 lean_dec_ref(x_673);
 x_714 = lean_box(0);
}
if (lean_is_scalar(x_714)) {
 x_715 = lean_alloc_ctor(1, 2, 0);
} else {
 x_715 = x_714;
}
lean_ctor_set(x_715, 0, x_712);
lean_ctor_set(x_715, 1, x_713);
return x_715;
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_665);
lean_dec(x_163);
lean_dec(x_158);
x_716 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_671);
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
lean_dec_ref(x_716);
x_719 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_718);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_722 = x_719;
} else {
 lean_dec_ref(x_719);
 x_722 = lean_box(0);
}
if (lean_is_scalar(x_662)) {
 x_723 = lean_alloc_ctor(0, 1, 0);
} else {
 x_723 = x_662;
 lean_ctor_set_tag(x_723, 0);
}
lean_ctor_set(x_723, 0, x_664);
if (lean_is_scalar(x_620)) {
 x_724 = lean_alloc_ctor(11, 1, 0);
} else {
 x_724 = x_620;
 lean_ctor_set_tag(x_724, 11);
}
lean_ctor_set(x_724, 0, x_723);
if (lean_is_scalar(x_20)) {
 x_725 = lean_alloc_ctor(0, 4, 0);
} else {
 x_725 = x_20;
}
lean_ctor_set(x_725, 0, x_717);
lean_ctor_set(x_725, 1, x_670);
lean_ctor_set(x_725, 2, x_724);
lean_ctor_set(x_725, 3, x_720);
if (lean_is_scalar(x_722)) {
 x_726 = lean_alloc_ctor(0, 2, 0);
} else {
 x_726 = x_722;
}
lean_ctor_set(x_726, 0, x_725);
lean_ctor_set(x_726, 1, x_721);
return x_726;
}
else
{
lean_dec(x_717);
lean_dec(x_670);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_620);
lean_dec(x_20);
return x_719;
}
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_620);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_727 = lean_ctor_get(x_669, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_669, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_729 = x_669;
} else {
 lean_dec_ref(x_669);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(1, 2, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_727);
lean_ctor_set(x_730, 1, x_728);
return x_730;
}
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_662);
lean_dec(x_620);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_731 = lean_ctor_get(x_666, 1);
lean_inc(x_731);
lean_dec_ref(x_666);
x_732 = lean_ctor_get(x_667, 0);
lean_inc(x_732);
lean_dec_ref(x_667);
x_733 = lean_st_ref_take(x_3, x_731);
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec_ref(x_733);
x_736 = lean_ctor_get(x_732, 1);
lean_inc(x_736);
x_737 = lean_ctor_get(x_732, 2);
lean_inc(x_737);
lean_dec(x_732);
x_738 = lean_ctor_get(x_734, 0);
lean_inc_ref(x_738);
x_739 = lean_ctor_get(x_734, 1);
lean_inc_ref(x_739);
x_740 = lean_ctor_get(x_734, 2);
lean_inc(x_740);
x_741 = lean_ctor_get(x_734, 3);
lean_inc_ref(x_741);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 lean_ctor_release(x_734, 2);
 lean_ctor_release(x_734, 3);
 x_742 = x_734;
} else {
 lean_dec_ref(x_734);
 x_742 = lean_box(0);
}
x_743 = lean_box(0);
x_744 = lean_nat_add(x_736, x_737);
lean_dec(x_737);
lean_dec(x_736);
x_745 = lean_array_get(x_743, x_159, x_744);
lean_dec(x_744);
lean_dec_ref(x_159);
x_746 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_741, x_17, x_745);
if (lean_is_scalar(x_742)) {
 x_747 = lean_alloc_ctor(0, 4, 0);
} else {
 x_747 = x_742;
}
lean_ctor_set(x_747, 0, x_738);
lean_ctor_set(x_747, 1, x_739);
lean_ctor_set(x_747, 2, x_740);
lean_ctor_set(x_747, 3, x_746);
x_748 = lean_st_ref_set(x_3, x_747, x_735);
x_749 = lean_ctor_get(x_748, 1);
lean_inc(x_749);
lean_dec_ref(x_748);
x_750 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_749);
return x_750;
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_662);
lean_dec(x_620);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_751 = lean_ctor_get(x_666, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_666, 1);
lean_inc(x_752);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 lean_ctor_release(x_666, 1);
 x_753 = x_666;
} else {
 lean_dec_ref(x_666);
 x_753 = lean_box(0);
}
if (lean_is_scalar(x_753)) {
 x_754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_754 = x_753;
}
lean_ctor_set(x_754, 0, x_751);
lean_ctor_set(x_754, 1, x_752);
return x_754;
}
}
case 7:
{
lean_object* x_755; lean_object* x_756; uint8_t x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_620);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 x_755 = x_619;
} else {
 lean_dec_ref(x_619);
 x_755 = lean_box(0);
}
x_756 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_757 = 1;
x_758 = l_Lean_Name_toString(x_158, x_757);
if (lean_is_scalar(x_755)) {
 x_759 = lean_alloc_ctor(3, 1, 0);
} else {
 x_759 = x_755;
 lean_ctor_set_tag(x_759, 3);
}
lean_ctor_set(x_759, 0, x_758);
x_760 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_760, 0, x_756);
lean_ctor_set(x_760, 1, x_759);
x_761 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_165, 5);
lean_ctor_set(x_165, 1, x_761);
lean_ctor_set(x_165, 0, x_760);
x_762 = l_Lean_MessageData_ofFormat(x_165);
x_763 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_762, x_4, x_5, x_614);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_763;
}
default: 
{
lean_object* x_764; 
lean_dec(x_620);
lean_dec(x_619);
lean_free_object(x_165);
lean_dec_ref(x_159);
lean_dec(x_20);
x_764 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_158, x_163, x_3, x_4, x_5, x_614);
return x_764;
}
}
}
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_free_object(x_165);
lean_dec_ref(x_159);
lean_dec(x_20);
x_765 = lean_ctor_get(x_171, 0);
lean_inc(x_765);
lean_dec_ref(x_171);
x_766 = lean_ctor_get(x_170, 1);
lean_inc(x_766);
lean_dec_ref(x_170);
x_767 = lean_ctor_get(x_765, 3);
lean_inc_ref(x_767);
lean_dec(x_765);
x_768 = lean_array_get_size(x_767);
lean_dec_ref(x_767);
x_769 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_158, x_768, x_163, x_3, x_4, x_5, x_766);
return x_769;
}
}
else
{
uint8_t x_770; 
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
x_770 = !lean_is_exclusive(x_170);
if (x_770 == 0)
{
return x_170;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_170, 0);
x_772 = lean_ctor_get(x_170, 1);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_170);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set(x_773, 1, x_772);
return x_773;
}
}
}
else
{
lean_object* x_774; lean_object* x_775; 
x_774 = lean_ctor_get(x_165, 1);
lean_inc(x_774);
lean_dec(x_165);
lean_inc(x_158);
x_775 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_158, x_5, x_774);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec_ref(x_775);
x_778 = lean_st_ref_get(x_5, x_777);
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_781 = x_778;
} else {
 lean_dec_ref(x_778);
 x_781 = lean_box(0);
}
x_782 = lean_ctor_get(x_779, 0);
lean_inc_ref(x_782);
lean_dec(x_779);
lean_inc(x_158);
x_783 = l_Lean_Environment_find_x3f(x_782, x_158, x_21);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; 
lean_dec(x_781);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_784 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_785 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_784, x_3, x_4, x_5, x_780);
return x_785;
}
else
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_783, 0);
lean_inc(x_786);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 x_787 = x_783;
} else {
 lean_dec_ref(x_783);
 x_787 = lean_box(0);
}
switch (lean_obj_tag(x_786)) {
case 0:
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_787);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 x_788 = x_786;
} else {
 lean_dec_ref(x_786);
 x_788 = lean_box(0);
}
x_789 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_790 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_791 = 1;
x_792 = l_Lean_Name_toString(x_158, x_791);
if (lean_is_scalar(x_788)) {
 x_793 = lean_alloc_ctor(3, 1, 0);
} else {
 x_793 = x_788;
 lean_ctor_set_tag(x_793, 3);
}
lean_ctor_set(x_793, 0, x_792);
if (lean_is_scalar(x_781)) {
 x_794 = lean_alloc_ctor(5, 2, 0);
} else {
 x_794 = x_781;
 lean_ctor_set_tag(x_794, 5);
}
lean_ctor_set(x_794, 0, x_790);
lean_ctor_set(x_794, 1, x_793);
x_795 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_796 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_795);
x_797 = l_Lean_MessageData_ofFormat(x_796);
x_798 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_789, x_797, x_4, x_5, x_780);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_798;
}
case 2:
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
lean_dec(x_787);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 x_799 = x_786;
} else {
 lean_dec_ref(x_786);
 x_799 = lean_box(0);
}
x_800 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_801 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_802 = 1;
x_803 = l_Lean_Name_toString(x_158, x_802);
if (lean_is_scalar(x_799)) {
 x_804 = lean_alloc_ctor(3, 1, 0);
} else {
 x_804 = x_799;
 lean_ctor_set_tag(x_804, 3);
}
lean_ctor_set(x_804, 0, x_803);
if (lean_is_scalar(x_781)) {
 x_805 = lean_alloc_ctor(5, 2, 0);
} else {
 x_805 = x_781;
 lean_ctor_set_tag(x_805, 5);
}
lean_ctor_set(x_805, 0, x_801);
lean_ctor_set(x_805, 1, x_804);
x_806 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_807 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
x_808 = l_Lean_MessageData_ofFormat(x_807);
x_809 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_800, x_808, x_4, x_5, x_780);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_809;
}
case 4:
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; uint8_t x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_787);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 x_810 = x_786;
} else {
 lean_dec_ref(x_786);
 x_810 = lean_box(0);
}
x_811 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_812 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_813 = 1;
x_814 = l_Lean_Name_toString(x_158, x_813);
if (lean_is_scalar(x_810)) {
 x_815 = lean_alloc_ctor(3, 1, 0);
} else {
 x_815 = x_810;
 lean_ctor_set_tag(x_815, 3);
}
lean_ctor_set(x_815, 0, x_814);
if (lean_is_scalar(x_781)) {
 x_816 = lean_alloc_ctor(5, 2, 0);
} else {
 x_816 = x_781;
 lean_ctor_set_tag(x_816, 5);
}
lean_ctor_set(x_816, 0, x_812);
lean_ctor_set(x_816, 1, x_815);
x_817 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_818 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set(x_818, 1, x_817);
x_819 = l_Lean_MessageData_ofFormat(x_818);
x_820 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_811, x_819, x_4, x_5, x_780);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_820;
}
case 5:
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; uint8_t x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_787);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 x_821 = x_786;
} else {
 lean_dec_ref(x_786);
 x_821 = lean_box(0);
}
x_822 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_823 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_824 = 1;
x_825 = l_Lean_Name_toString(x_158, x_824);
if (lean_is_scalar(x_821)) {
 x_826 = lean_alloc_ctor(3, 1, 0);
} else {
 x_826 = x_821;
 lean_ctor_set_tag(x_826, 3);
}
lean_ctor_set(x_826, 0, x_825);
if (lean_is_scalar(x_781)) {
 x_827 = lean_alloc_ctor(5, 2, 0);
} else {
 x_827 = x_781;
 lean_ctor_set_tag(x_827, 5);
}
lean_ctor_set(x_827, 0, x_823);
lean_ctor_set(x_827, 1, x_826);
x_828 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_829 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_829, 0, x_827);
lean_ctor_set(x_829, 1, x_828);
x_830 = l_Lean_MessageData_ofFormat(x_829);
x_831 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_822, x_830, x_4, x_5, x_780);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_831;
}
case 6:
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_781);
lean_inc(x_17);
lean_dec_ref(x_1);
x_832 = lean_ctor_get(x_786, 0);
lean_inc_ref(x_832);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 x_833 = x_786;
} else {
 lean_dec_ref(x_786);
 x_833 = lean_box(0);
}
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
x_835 = lean_ctor_get(x_832, 2);
lean_inc(x_835);
x_836 = lean_ctor_get(x_832, 3);
lean_inc(x_836);
lean_dec_ref(x_832);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_834);
x_837 = l_Lean_IR_hasTrivialStructure_x3f(x_834, x_4, x_5, x_780);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; 
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; 
lean_dec_ref(x_159);
x_839 = lean_ctor_get(x_837, 1);
lean_inc(x_839);
lean_dec_ref(x_837);
lean_inc(x_5);
lean_inc_ref(x_4);
x_840 = l_Lean_IR_nameToIRType(x_834, x_4, x_5, x_839);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; lean_object* x_842; uint8_t x_843; 
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
lean_dec_ref(x_840);
x_843 = l_Lean_IR_IRType_isScalar(x_841);
if (x_843 == 0)
{
lean_object* x_844; 
lean_dec(x_841);
lean_dec(x_835);
lean_dec(x_833);
lean_dec(x_787);
lean_inc(x_5);
lean_inc_ref(x_4);
x_844 = l_Lean_IR_getCtorLayout(x_158, x_4, x_5, x_842);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_870; lean_object* x_871; uint8_t x_872; 
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_844, 1);
lean_inc(x_846);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_847 = x_844;
} else {
 lean_dec_ref(x_844);
 x_847 = lean_box(0);
}
x_851 = lean_ctor_get(x_845, 0);
lean_inc_ref(x_851);
x_852 = lean_ctor_get(x_845, 1);
lean_inc_ref(x_852);
lean_dec(x_845);
x_853 = lean_array_get_size(x_163);
x_854 = l_Array_extract___redArg(x_163, x_836, x_853);
lean_dec(x_163);
x_870 = lean_array_get_size(x_854);
x_871 = lean_array_get_size(x_852);
x_872 = lean_nat_dec_eq(x_870, x_871);
lean_dec(x_870);
if (x_872 == 0)
{
lean_dec(x_871);
lean_dec_ref(x_854);
lean_dec_ref(x_852);
lean_dec_ref(x_851);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_850;
}
else
{
if (x_843 == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; uint8_t x_878; 
lean_dec(x_847);
x_873 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0;
x_874 = lean_unsigned_to_nat(0u);
x_875 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_876 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_873);
lean_inc(x_871);
x_877 = lean_apply_2(x_876, x_871, x_874);
x_878 = lean_unbox(x_877);
if (x_878 == 0)
{
lean_dec(x_871);
x_855 = x_875;
x_856 = x_846;
goto block_869;
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
x_879 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_880 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_852, x_879, x_854, x_871, x_875, x_874, x_846);
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec_ref(x_880);
x_855 = x_881;
x_856 = x_882;
goto block_869;
}
}
else
{
lean_dec(x_871);
lean_dec_ref(x_854);
lean_dec_ref(x_852);
lean_dec_ref(x_851);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_850;
}
}
block_850:
{
lean_object* x_848; lean_object* x_849; 
x_848 = lean_box(12);
if (lean_is_scalar(x_847)) {
 x_849 = lean_alloc_ctor(0, 2, 0);
} else {
 x_849 = x_847;
}
lean_ctor_set(x_849, 0, x_848);
lean_ctor_set(x_849, 1, x_846);
return x_849;
}
block_869:
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_857 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_856);
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_860 = x_857;
} else {
 lean_dec_ref(x_857);
 x_860 = lean_box(0);
}
lean_inc(x_858);
x_861 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_851, x_852, x_854, x_858, x_3, x_4, x_5, x_859);
lean_dec_ref(x_854);
lean_dec_ref(x_852);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 lean_ctor_release(x_861, 1);
 x_864 = x_861;
} else {
 lean_dec_ref(x_861);
 x_864 = lean_box(0);
}
x_865 = l_Lean_IR_CtorInfo_type(x_851);
if (lean_is_scalar(x_860)) {
 x_866 = lean_alloc_ctor(0, 2, 0);
} else {
 x_866 = x_860;
}
lean_ctor_set(x_866, 0, x_851);
lean_ctor_set(x_866, 1, x_855);
if (lean_is_scalar(x_20)) {
 x_867 = lean_alloc_ctor(0, 4, 0);
} else {
 x_867 = x_20;
}
lean_ctor_set(x_867, 0, x_858);
lean_ctor_set(x_867, 1, x_865);
lean_ctor_set(x_867, 2, x_866);
lean_ctor_set(x_867, 3, x_862);
if (lean_is_scalar(x_864)) {
 x_868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_868 = x_864;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_863);
return x_868;
}
else
{
lean_dec(x_860);
lean_dec(x_858);
lean_dec_ref(x_855);
lean_dec_ref(x_851);
lean_dec(x_20);
return x_861;
}
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_836);
lean_dec(x_163);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_883 = lean_ctor_get(x_844, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_844, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_885 = x_844;
} else {
 lean_dec_ref(x_844);
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
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_836);
lean_dec(x_163);
lean_dec(x_158);
x_887 = l_Lean_IR_ToIR_bindVar___redArg(x_17, x_3, x_842);
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
lean_dec_ref(x_887);
x_890 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_889);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_893 = x_890;
} else {
 lean_dec_ref(x_890);
 x_893 = lean_box(0);
}
if (lean_is_scalar(x_833)) {
 x_894 = lean_alloc_ctor(0, 1, 0);
} else {
 x_894 = x_833;
 lean_ctor_set_tag(x_894, 0);
}
lean_ctor_set(x_894, 0, x_835);
if (lean_is_scalar(x_787)) {
 x_895 = lean_alloc_ctor(11, 1, 0);
} else {
 x_895 = x_787;
 lean_ctor_set_tag(x_895, 11);
}
lean_ctor_set(x_895, 0, x_894);
if (lean_is_scalar(x_20)) {
 x_896 = lean_alloc_ctor(0, 4, 0);
} else {
 x_896 = x_20;
}
lean_ctor_set(x_896, 0, x_888);
lean_ctor_set(x_896, 1, x_841);
lean_ctor_set(x_896, 2, x_895);
lean_ctor_set(x_896, 3, x_891);
if (lean_is_scalar(x_893)) {
 x_897 = lean_alloc_ctor(0, 2, 0);
} else {
 x_897 = x_893;
}
lean_ctor_set(x_897, 0, x_896);
lean_ctor_set(x_897, 1, x_892);
return x_897;
}
else
{
lean_dec(x_888);
lean_dec(x_841);
lean_dec(x_835);
lean_dec(x_833);
lean_dec(x_787);
lean_dec(x_20);
return x_890;
}
}
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_833);
lean_dec(x_787);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_898 = lean_ctor_get(x_840, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_840, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 lean_ctor_release(x_840, 1);
 x_900 = x_840;
} else {
 lean_dec_ref(x_840);
 x_900 = lean_box(0);
}
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(1, 2, 0);
} else {
 x_901 = x_900;
}
lean_ctor_set(x_901, 0, x_898);
lean_ctor_set(x_901, 1, x_899);
return x_901;
}
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_834);
lean_dec(x_833);
lean_dec(x_787);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_20);
x_902 = lean_ctor_get(x_837, 1);
lean_inc(x_902);
lean_dec_ref(x_837);
x_903 = lean_ctor_get(x_838, 0);
lean_inc(x_903);
lean_dec_ref(x_838);
x_904 = lean_st_ref_take(x_3, x_902);
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
lean_dec_ref(x_904);
x_907 = lean_ctor_get(x_903, 1);
lean_inc(x_907);
x_908 = lean_ctor_get(x_903, 2);
lean_inc(x_908);
lean_dec(x_903);
x_909 = lean_ctor_get(x_905, 0);
lean_inc_ref(x_909);
x_910 = lean_ctor_get(x_905, 1);
lean_inc_ref(x_910);
x_911 = lean_ctor_get(x_905, 2);
lean_inc(x_911);
x_912 = lean_ctor_get(x_905, 3);
lean_inc_ref(x_912);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 lean_ctor_release(x_905, 2);
 lean_ctor_release(x_905, 3);
 x_913 = x_905;
} else {
 lean_dec_ref(x_905);
 x_913 = lean_box(0);
}
x_914 = lean_box(0);
x_915 = lean_nat_add(x_907, x_908);
lean_dec(x_908);
lean_dec(x_907);
x_916 = lean_array_get(x_914, x_159, x_915);
lean_dec(x_915);
lean_dec_ref(x_159);
x_917 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_IR_ToIR_lowerCode_spec__3___redArg(x_912, x_17, x_916);
if (lean_is_scalar(x_913)) {
 x_918 = lean_alloc_ctor(0, 4, 0);
} else {
 x_918 = x_913;
}
lean_ctor_set(x_918, 0, x_909);
lean_ctor_set(x_918, 1, x_910);
lean_ctor_set(x_918, 2, x_911);
lean_ctor_set(x_918, 3, x_917);
x_919 = lean_st_ref_set(x_3, x_918, x_906);
x_920 = lean_ctor_get(x_919, 1);
lean_inc(x_920);
lean_dec_ref(x_919);
x_921 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_920);
return x_921;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_834);
lean_dec(x_833);
lean_dec(x_787);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_922 = lean_ctor_get(x_837, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_837, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_924 = x_837;
} else {
 lean_dec_ref(x_837);
 x_924 = lean_box(0);
}
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(1, 2, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_922);
lean_ctor_set(x_925, 1, x_923);
return x_925;
}
}
case 7:
{
lean_object* x_926; lean_object* x_927; uint8_t x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
lean_dec(x_787);
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_20);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 x_926 = x_786;
} else {
 lean_dec_ref(x_786);
 x_926 = lean_box(0);
}
x_927 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_928 = 1;
x_929 = l_Lean_Name_toString(x_158, x_928);
if (lean_is_scalar(x_926)) {
 x_930 = lean_alloc_ctor(3, 1, 0);
} else {
 x_930 = x_926;
 lean_ctor_set_tag(x_930, 3);
}
lean_ctor_set(x_930, 0, x_929);
if (lean_is_scalar(x_781)) {
 x_931 = lean_alloc_ctor(5, 2, 0);
} else {
 x_931 = x_781;
 lean_ctor_set_tag(x_931, 5);
}
lean_ctor_set(x_931, 0, x_927);
lean_ctor_set(x_931, 1, x_930);
x_932 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_933 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_933, 0, x_931);
lean_ctor_set(x_933, 1, x_932);
x_934 = l_Lean_MessageData_ofFormat(x_933);
x_935 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_934, x_4, x_5, x_780);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_935;
}
default: 
{
lean_object* x_936; 
lean_dec(x_787);
lean_dec(x_786);
lean_dec(x_781);
lean_dec_ref(x_159);
lean_dec(x_20);
x_936 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_158, x_163, x_3, x_4, x_5, x_780);
return x_936;
}
}
}
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec_ref(x_159);
lean_dec(x_20);
x_937 = lean_ctor_get(x_776, 0);
lean_inc(x_937);
lean_dec_ref(x_776);
x_938 = lean_ctor_get(x_775, 1);
lean_inc(x_938);
lean_dec_ref(x_775);
x_939 = lean_ctor_get(x_937, 3);
lean_inc_ref(x_939);
lean_dec(x_937);
x_940 = lean_array_get_size(x_939);
lean_dec_ref(x_939);
x_941 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_158, x_940, x_163, x_3, x_4, x_5, x_938);
return x_941;
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
lean_dec(x_163);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_942 = lean_ctor_get(x_775, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_775, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_944 = x_775;
} else {
 lean_dec_ref(x_775);
 x_944 = lean_box(0);
}
if (lean_is_scalar(x_944)) {
 x_945 = lean_alloc_ctor(1, 2, 0);
} else {
 x_945 = x_944;
}
lean_ctor_set(x_945, 0, x_942);
lean_ctor_set(x_945, 1, x_943);
return x_945;
}
}
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
lean_dec_ref(x_159);
lean_dec(x_20);
x_946 = lean_ctor_get(x_165, 1);
lean_inc(x_946);
lean_dec_ref(x_165);
x_947 = lean_ctor_get(x_166, 0);
lean_inc(x_947);
lean_dec_ref(x_166);
x_948 = l_Lean_IR_Decl_params(x_947);
lean_dec(x_947);
x_949 = lean_array_get_size(x_948);
lean_dec_ref(x_948);
x_950 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_158, x_949, x_163, x_3, x_4, x_5, x_946);
return x_950;
}
}
default: 
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_20);
x_951 = lean_ctor_get(x_22, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_952);
lean_dec_ref(x_22);
x_953 = l_Lean_IR_ToIR_getFVarValue___redArg(x_951, x_3, x_16);
x_954 = lean_ctor_get(x_953, 0);
lean_inc(x_954);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; size_t x_957; size_t x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_955 = lean_ctor_get(x_953, 1);
lean_inc(x_955);
lean_dec_ref(x_953);
x_956 = lean_ctor_get(x_954, 0);
lean_inc(x_956);
lean_dec_ref(x_954);
x_957 = lean_array_size(x_952);
x_958 = 0;
x_959 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_957, x_958, x_952, x_3, x_955);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
lean_dec_ref(x_959);
x_962 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(x_1, x_2, x_956, x_960, x_3, x_4, x_5, x_961);
return x_962;
}
else
{
lean_object* x_963; lean_object* x_964; 
lean_dec_ref(x_952);
x_963 = lean_ctor_get(x_953, 1);
lean_inc(x_963);
lean_dec_ref(x_953);
x_964 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_963);
return x_964;
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
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_5);
x_20 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_20;
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
x_3 = lean_unsigned_to_nat(329u);
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
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__0);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__1 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__1();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerCode_spec__5___redArg___closed__1);
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
