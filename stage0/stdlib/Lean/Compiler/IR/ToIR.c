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
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__11;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
lean_object* l_Lean_IR_CtorInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__16;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__5;
static lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2;
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity_spec__0(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__14;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_BuilderState_ctorIdx(lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__4;
lean_object* l_Lean_IR_IRType_boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0_spec__0___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_IR_nameToIRType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__1;
static lean_object* l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx___boxed(lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
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
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_14 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_13, x_12, x_1);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_19, x_1, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_21, x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_st_ref_set(x_2, x_26, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_28);
return x_30;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_19, x_1, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
x_25 = lean_st_ref_set(x_3, x_24, x_7);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_20);
x_21 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_19, x_1, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_20, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
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
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_26);
return x_28;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_21 = lean_box(1);
x_22 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___Lean_IR_ToIR_bindVar_spec__0___redArg(x_18, x_1, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
x_24 = lean_st_ref_set(x_2, x_23, x_6);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
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
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
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
static lean_object* _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__3() {
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
x_26 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__3;
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
x_44 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__3;
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
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
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
x_65 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__3;
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
x_3 = lean_unsigned_to_nat(274u);
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
x_3 = lean_unsigned_to_nat(129u);
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
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_unsigned_to_nat(121u);
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
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_62);
lean_dec_ref(x_66);
lean_dec(x_64);
x_91 = lean_ctor_get(x_68, 1);
lean_inc(x_91);
lean_dec_ref(x_68);
x_92 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_93 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_92, x_2, x_3, x_4, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_62, 0);
x_95 = lean_ctor_get(x_62, 2);
x_96 = lean_ctor_get(x_62, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_62);
x_97 = l_Lean_IR_ToIR_getFVarValue___redArg(x_95, x_2, x_5);
lean_dec(x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec_ref(x_98);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_94);
x_101 = l_Lean_IR_nameToIRType(x_94, x_3, x_4, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_array_size(x_96);
x_105 = 0;
lean_inc(x_100);
x_106 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_100, x_104, x_105, x_96, x_2, x_3, x_4, x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_110, 0, x_94);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_102);
lean_ctor_set(x_110, 3, x_107);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_94);
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_114 = x_106;
} else {
 lean_dec_ref(x_106);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_100);
lean_dec_ref(x_96);
lean_dec(x_94);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_101, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_101, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_118 = x_101;
} else {
 lean_dec_ref(x_101);
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
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_96);
lean_dec(x_94);
x_120 = lean_ctor_get(x_97, 1);
lean_inc(x_120);
lean_dec_ref(x_97);
x_121 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_122 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_121, x_2, x_3, x_4, x_120);
return x_122;
}
}
}
case 5:
{
uint8_t x_123; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_123 = !lean_is_exclusive(x_1);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_1, 0);
x_125 = l_Lean_IR_ToIR_getFVarValue___redArg(x_124, x_2, x_5);
lean_dec(x_2);
lean_dec(x_124);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_125, 0);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_127);
lean_ctor_set(x_125, 0, x_1);
return x_125;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_125, 0);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_125);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_1);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_1, 0);
lean_inc(x_131);
lean_dec(x_1);
x_132 = l_Lean_IR_ToIR_getFVarValue___redArg(x_131, x_2, x_5);
lean_dec(x_2);
lean_dec(x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_136, 0, x_133);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
}
default: 
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_138 = lean_box(12);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_5);
return x_139;
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
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_unsigned_to_nat(141u);
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
x_3 = lean_unsigned_to_nat(206u);
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
lean_object* x_168; lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_168 = lean_ctor_get(x_1, 0);
x_169 = lean_ctor_get(x_14, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_170);
lean_dec_ref(x_14);
x_171 = lean_array_size(x_170);
x_172 = 0;
x_173 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_171, x_172, x_170, x_3, x_6);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec_ref(x_173);
lean_inc(x_169);
x_176 = l_Lean_IR_ToIR_findDecl___redArg(x_169, x_5, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_176);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_176, 1);
x_180 = lean_ctor_get(x_176, 0);
lean_dec(x_180);
lean_inc(x_169);
x_181 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_169, x_5, x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec_ref(x_181);
x_184 = lean_st_ref_get(x_5, x_183);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_184, 0);
x_187 = lean_ctor_get(x_184, 1);
x_188 = lean_ctor_get(x_186, 0);
lean_inc_ref(x_188);
lean_dec(x_186);
x_189 = 0;
lean_inc(x_169);
x_190 = l_Lean_Environment_find_x3f(x_188, x_169, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
lean_free_object(x_184);
lean_free_object(x_176);
lean_dec(x_174);
lean_dec(x_169);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_191 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_192 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_191, x_3, x_4, x_5, x_187);
return x_192;
}
else
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_190);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_190, 0);
switch (lean_obj_tag(x_194)) {
case 0:
{
uint8_t x_195; 
lean_free_object(x_190);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = lean_ctor_get(x_194, 0);
lean_dec(x_196);
x_197 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_198 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_199 = 1;
x_200 = l_Lean_Name_toString(x_169, x_199);
lean_ctor_set_tag(x_194, 3);
lean_ctor_set(x_194, 0, x_200);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_194);
lean_ctor_set(x_184, 0, x_198);
x_201 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_201);
lean_ctor_set(x_176, 0, x_184);
x_202 = l_Lean_MessageData_ofFormat(x_176);
x_203 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_197, x_202, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_194);
x_204 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_205 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_206 = 1;
x_207 = l_Lean_Name_toString(x_169, x_206);
x_208 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_208);
lean_ctor_set(x_184, 0, x_205);
x_209 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_209);
lean_ctor_set(x_176, 0, x_184);
x_210 = l_Lean_MessageData_ofFormat(x_176);
x_211 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_204, x_210, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_211;
}
}
case 2:
{
uint8_t x_212; 
lean_free_object(x_190);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_212 = !lean_is_exclusive(x_194);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_213 = lean_ctor_get(x_194, 0);
lean_dec(x_213);
x_214 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_215 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_216 = 1;
x_217 = l_Lean_Name_toString(x_169, x_216);
lean_ctor_set_tag(x_194, 3);
lean_ctor_set(x_194, 0, x_217);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_194);
lean_ctor_set(x_184, 0, x_215);
x_218 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_218);
lean_ctor_set(x_176, 0, x_184);
x_219 = l_Lean_MessageData_ofFormat(x_176);
x_220 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_214, x_219, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_194);
x_221 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_222 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_223 = 1;
x_224 = l_Lean_Name_toString(x_169, x_223);
x_225 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_225);
lean_ctor_set(x_184, 0, x_222);
x_226 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_226);
lean_ctor_set(x_176, 0, x_184);
x_227 = l_Lean_MessageData_ofFormat(x_176);
x_228 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_221, x_227, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_228;
}
}
case 4:
{
uint8_t x_229; 
lean_free_object(x_190);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_229 = !lean_is_exclusive(x_194);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_230 = lean_ctor_get(x_194, 0);
lean_dec(x_230);
x_231 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_232 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_233 = 1;
x_234 = l_Lean_Name_toString(x_169, x_233);
lean_ctor_set_tag(x_194, 3);
lean_ctor_set(x_194, 0, x_234);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_194);
lean_ctor_set(x_184, 0, x_232);
x_235 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_235);
lean_ctor_set(x_176, 0, x_184);
x_236 = l_Lean_MessageData_ofFormat(x_176);
x_237 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_231, x_236, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_194);
x_238 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_239 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_240 = 1;
x_241 = l_Lean_Name_toString(x_169, x_240);
x_242 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_242);
lean_ctor_set(x_184, 0, x_239);
x_243 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_243);
lean_ctor_set(x_176, 0, x_184);
x_244 = l_Lean_MessageData_ofFormat(x_176);
x_245 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_238, x_244, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_245;
}
}
case 5:
{
uint8_t x_246; 
lean_free_object(x_190);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_246 = !lean_is_exclusive(x_194);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_247 = lean_ctor_get(x_194, 0);
lean_dec(x_247);
x_248 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_249 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_250 = 1;
x_251 = l_Lean_Name_toString(x_169, x_250);
lean_ctor_set_tag(x_194, 3);
lean_ctor_set(x_194, 0, x_251);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_194);
lean_ctor_set(x_184, 0, x_249);
x_252 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_252);
lean_ctor_set(x_176, 0, x_184);
x_253 = l_Lean_MessageData_ofFormat(x_176);
x_254 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_248, x_253, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_194);
x_255 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_256 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_257 = 1;
x_258 = l_Lean_Name_toString(x_169, x_257);
x_259 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_259);
lean_ctor_set(x_184, 0, x_256);
x_260 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_260);
lean_ctor_set(x_176, 0, x_184);
x_261 = l_Lean_MessageData_ofFormat(x_176);
x_262 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_255, x_261, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_262;
}
}
case 6:
{
lean_object* x_263; uint8_t x_264; 
lean_free_object(x_184);
lean_free_object(x_176);
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_263 = x_1;
} else {
 lean_dec_ref(x_1);
 x_263 = lean_box(0);
}
x_264 = !lean_is_exclusive(x_194);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_194, 0);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 2);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 3);
lean_inc(x_268);
lean_dec_ref(x_265);
lean_inc(x_5);
lean_inc_ref(x_4);
x_269 = l_Lean_IR_nameToIRType(x_266, x_4, x_5, x_187);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec_ref(x_269);
x_272 = l_Lean_IR_IRType_isScalar(x_270);
if (x_272 == 0)
{
lean_object* x_273; 
lean_dec(x_270);
lean_dec(x_267);
lean_free_object(x_194);
lean_free_object(x_190);
lean_inc(x_5);
lean_inc_ref(x_4);
x_273 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_271);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
x_280 = lean_ctor_get(x_274, 0);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_274, 1);
lean_inc_ref(x_281);
lean_dec(x_274);
x_282 = lean_array_get_size(x_174);
x_283 = l_Array_extract___redArg(x_174, x_268, x_282);
lean_dec(x_174);
x_311 = lean_array_get_size(x_283);
x_312 = lean_array_get_size(x_281);
x_313 = lean_nat_dec_eq(x_311, x_312);
lean_dec(x_311);
if (x_313 == 0)
{
lean_dec(x_312);
lean_dec_ref(x_283);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec(x_263);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_279;
}
else
{
if (x_272 == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
lean_dec(x_276);
x_314 = lean_unsigned_to_nat(0u);
x_315 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_316 = lean_nat_dec_lt(x_314, x_312);
if (x_316 == 0)
{
lean_dec(x_312);
x_284 = x_315;
x_285 = x_275;
goto block_310;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_318 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_281, x_317, x_283, x_312, x_315, x_314, x_275);
lean_dec(x_312);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec_ref(x_318);
x_284 = x_319;
x_285 = x_320;
goto block_310;
}
}
else
{
lean_dec(x_312);
lean_dec_ref(x_283);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec(x_263);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_279;
}
}
block_279:
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_box(12);
if (lean_is_scalar(x_276)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_276;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
return x_278;
}
block_310:
{
lean_object* x_286; uint8_t x_287; 
x_286 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_285);
x_287 = !lean_is_exclusive(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_286, 0);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
x_290 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_280, x_281, x_283, x_288, x_3, x_4, x_5, x_289);
lean_dec_ref(x_283);
lean_dec_ref(x_281);
if (lean_obj_tag(x_290) == 0)
{
uint8_t x_291; 
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_290, 0);
x_293 = l_Lean_IR_CtorInfo_type(x_280);
lean_ctor_set(x_286, 1, x_284);
lean_ctor_set(x_286, 0, x_280);
if (lean_is_scalar(x_263)) {
 x_294 = lean_alloc_ctor(0, 4, 0);
} else {
 x_294 = x_263;
}
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_294, 2, x_286);
lean_ctor_set(x_294, 3, x_292);
lean_ctor_set(x_290, 0, x_294);
return x_290;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_295 = lean_ctor_get(x_290, 0);
x_296 = lean_ctor_get(x_290, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_290);
x_297 = l_Lean_IR_CtorInfo_type(x_280);
lean_ctor_set(x_286, 1, x_284);
lean_ctor_set(x_286, 0, x_280);
if (lean_is_scalar(x_263)) {
 x_298 = lean_alloc_ctor(0, 4, 0);
} else {
 x_298 = x_263;
}
lean_ctor_set(x_298, 0, x_288);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_298, 2, x_286);
lean_ctor_set(x_298, 3, x_295);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_296);
return x_299;
}
}
else
{
lean_free_object(x_286);
lean_dec(x_288);
lean_dec_ref(x_284);
lean_dec_ref(x_280);
lean_dec(x_263);
return x_290;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_286, 0);
x_301 = lean_ctor_get(x_286, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_286);
lean_inc(x_300);
x_302 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_280, x_281, x_283, x_300, x_3, x_4, x_5, x_301);
lean_dec_ref(x_283);
lean_dec_ref(x_281);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
x_306 = l_Lean_IR_CtorInfo_type(x_280);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_280);
lean_ctor_set(x_307, 1, x_284);
if (lean_is_scalar(x_263)) {
 x_308 = lean_alloc_ctor(0, 4, 0);
} else {
 x_308 = x_263;
}
lean_ctor_set(x_308, 0, x_300);
lean_ctor_set(x_308, 1, x_306);
lean_ctor_set(x_308, 2, x_307);
lean_ctor_set(x_308, 3, x_303);
if (lean_is_scalar(x_305)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_305;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_304);
return x_309;
}
else
{
lean_dec(x_300);
lean_dec_ref(x_284);
lean_dec_ref(x_280);
lean_dec(x_263);
return x_302;
}
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_268);
lean_dec(x_263);
lean_dec(x_174);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_321 = !lean_is_exclusive(x_273);
if (x_321 == 0)
{
return x_273;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_273, 0);
x_323 = lean_ctor_get(x_273, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_273);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_268);
lean_dec(x_174);
lean_dec(x_169);
x_325 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_271);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec_ref(x_325);
x_328 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_327);
if (lean_obj_tag(x_328) == 0)
{
uint8_t x_329; 
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; 
x_330 = lean_ctor_get(x_328, 0);
lean_ctor_set_tag(x_194, 0);
lean_ctor_set(x_194, 0, x_267);
lean_ctor_set_tag(x_190, 11);
if (lean_is_scalar(x_263)) {
 x_331 = lean_alloc_ctor(0, 4, 0);
} else {
 x_331 = x_263;
}
lean_ctor_set(x_331, 0, x_326);
lean_ctor_set(x_331, 1, x_270);
lean_ctor_set(x_331, 2, x_190);
lean_ctor_set(x_331, 3, x_330);
lean_ctor_set(x_328, 0, x_331);
return x_328;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_328, 0);
x_333 = lean_ctor_get(x_328, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_328);
lean_ctor_set_tag(x_194, 0);
lean_ctor_set(x_194, 0, x_267);
lean_ctor_set_tag(x_190, 11);
if (lean_is_scalar(x_263)) {
 x_334 = lean_alloc_ctor(0, 4, 0);
} else {
 x_334 = x_263;
}
lean_ctor_set(x_334, 0, x_326);
lean_ctor_set(x_334, 1, x_270);
lean_ctor_set(x_334, 2, x_190);
lean_ctor_set(x_334, 3, x_332);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
else
{
lean_dec(x_326);
lean_dec(x_270);
lean_dec(x_267);
lean_free_object(x_194);
lean_dec(x_263);
lean_free_object(x_190);
return x_328;
}
}
}
else
{
uint8_t x_336; 
lean_dec(x_268);
lean_dec(x_267);
lean_free_object(x_194);
lean_dec(x_263);
lean_free_object(x_190);
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_336 = !lean_is_exclusive(x_269);
if (x_336 == 0)
{
return x_269;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_269, 0);
x_338 = lean_ctor_get(x_269, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_269);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_194, 0);
lean_inc(x_340);
lean_dec(x_194);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 2);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 3);
lean_inc(x_343);
lean_dec_ref(x_340);
lean_inc(x_5);
lean_inc_ref(x_4);
x_344 = l_Lean_IR_nameToIRType(x_341, x_4, x_5, x_187);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec_ref(x_344);
x_347 = l_Lean_IR_IRType_isScalar(x_345);
if (x_347 == 0)
{
lean_object* x_348; 
lean_dec(x_345);
lean_dec(x_342);
lean_free_object(x_190);
lean_inc(x_5);
lean_inc_ref(x_4);
x_348 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_346);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_351 = x_348;
} else {
 lean_dec_ref(x_348);
 x_351 = lean_box(0);
}
x_355 = lean_ctor_get(x_349, 0);
lean_inc_ref(x_355);
x_356 = lean_ctor_get(x_349, 1);
lean_inc_ref(x_356);
lean_dec(x_349);
x_357 = lean_array_get_size(x_174);
x_358 = l_Array_extract___redArg(x_174, x_343, x_357);
lean_dec(x_174);
x_374 = lean_array_get_size(x_358);
x_375 = lean_array_get_size(x_356);
x_376 = lean_nat_dec_eq(x_374, x_375);
lean_dec(x_374);
if (x_376 == 0)
{
lean_dec(x_375);
lean_dec_ref(x_358);
lean_dec_ref(x_356);
lean_dec_ref(x_355);
lean_dec(x_263);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_354;
}
else
{
if (x_347 == 0)
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; 
lean_dec(x_351);
x_377 = lean_unsigned_to_nat(0u);
x_378 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_379 = lean_nat_dec_lt(x_377, x_375);
if (x_379 == 0)
{
lean_dec(x_375);
x_359 = x_378;
x_360 = x_350;
goto block_373;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_380 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_381 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_356, x_380, x_358, x_375, x_378, x_377, x_350);
lean_dec(x_375);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec_ref(x_381);
x_359 = x_382;
x_360 = x_383;
goto block_373;
}
}
else
{
lean_dec(x_375);
lean_dec_ref(x_358);
lean_dec_ref(x_356);
lean_dec_ref(x_355);
lean_dec(x_263);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_354;
}
}
block_354:
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_box(12);
if (lean_is_scalar(x_351)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_351;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_350);
return x_353;
}
block_373:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_361 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_360);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_364 = x_361;
} else {
 lean_dec_ref(x_361);
 x_364 = lean_box(0);
}
lean_inc(x_362);
x_365 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_355, x_356, x_358, x_362, x_3, x_4, x_5, x_363);
lean_dec_ref(x_358);
lean_dec_ref(x_356);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_368 = x_365;
} else {
 lean_dec_ref(x_365);
 x_368 = lean_box(0);
}
x_369 = l_Lean_IR_CtorInfo_type(x_355);
if (lean_is_scalar(x_364)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_364;
}
lean_ctor_set(x_370, 0, x_355);
lean_ctor_set(x_370, 1, x_359);
if (lean_is_scalar(x_263)) {
 x_371 = lean_alloc_ctor(0, 4, 0);
} else {
 x_371 = x_263;
}
lean_ctor_set(x_371, 0, x_362);
lean_ctor_set(x_371, 1, x_369);
lean_ctor_set(x_371, 2, x_370);
lean_ctor_set(x_371, 3, x_366);
if (lean_is_scalar(x_368)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_368;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_367);
return x_372;
}
else
{
lean_dec(x_364);
lean_dec(x_362);
lean_dec_ref(x_359);
lean_dec_ref(x_355);
lean_dec(x_263);
return x_365;
}
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_343);
lean_dec(x_263);
lean_dec(x_174);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_384 = lean_ctor_get(x_348, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_348, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_386 = x_348;
} else {
 lean_dec_ref(x_348);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_385);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_343);
lean_dec(x_174);
lean_dec(x_169);
x_388 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_346);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec_ref(x_388);
x_391 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_390);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_394 = x_391;
} else {
 lean_dec_ref(x_391);
 x_394 = lean_box(0);
}
x_395 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_395, 0, x_342);
lean_ctor_set_tag(x_190, 11);
lean_ctor_set(x_190, 0, x_395);
if (lean_is_scalar(x_263)) {
 x_396 = lean_alloc_ctor(0, 4, 0);
} else {
 x_396 = x_263;
}
lean_ctor_set(x_396, 0, x_389);
lean_ctor_set(x_396, 1, x_345);
lean_ctor_set(x_396, 2, x_190);
lean_ctor_set(x_396, 3, x_392);
if (lean_is_scalar(x_394)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_394;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_393);
return x_397;
}
else
{
lean_dec(x_389);
lean_dec(x_345);
lean_dec(x_342);
lean_dec(x_263);
lean_free_object(x_190);
return x_391;
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_263);
lean_free_object(x_190);
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_398 = lean_ctor_get(x_344, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_344, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_400 = x_344;
} else {
 lean_dec_ref(x_344);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
}
case 7:
{
uint8_t x_402; 
lean_free_object(x_190);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_402 = !lean_is_exclusive(x_194);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_403 = lean_ctor_get(x_194, 0);
lean_dec(x_403);
x_404 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_405 = 1;
x_406 = l_Lean_Name_toString(x_169, x_405);
lean_ctor_set_tag(x_194, 3);
lean_ctor_set(x_194, 0, x_406);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_194);
lean_ctor_set(x_184, 0, x_404);
x_407 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_407);
lean_ctor_set(x_176, 0, x_184);
x_408 = l_Lean_MessageData_ofFormat(x_176);
x_409 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_408, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_409;
}
else
{
lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_194);
x_410 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_411 = 1;
x_412 = l_Lean_Name_toString(x_169, x_411);
x_413 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_413);
lean_ctor_set(x_184, 0, x_410);
x_414 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_414);
lean_ctor_set(x_176, 0, x_184);
x_415 = l_Lean_MessageData_ofFormat(x_176);
x_416 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_415, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_416;
}
}
default: 
{
lean_object* x_417; 
lean_free_object(x_190);
lean_dec(x_194);
lean_free_object(x_184);
lean_free_object(x_176);
x_417 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_174, x_3, x_4, x_5, x_187);
return x_417;
}
}
}
else
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_190, 0);
lean_inc(x_418);
lean_dec(x_190);
switch (lean_obj_tag(x_418)) {
case 0:
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_419 = x_418;
} else {
 lean_dec_ref(x_418);
 x_419 = lean_box(0);
}
x_420 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_421 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_422 = 1;
x_423 = l_Lean_Name_toString(x_169, x_422);
if (lean_is_scalar(x_419)) {
 x_424 = lean_alloc_ctor(3, 1, 0);
} else {
 x_424 = x_419;
 lean_ctor_set_tag(x_424, 3);
}
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_424);
lean_ctor_set(x_184, 0, x_421);
x_425 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_425);
lean_ctor_set(x_176, 0, x_184);
x_426 = l_Lean_MessageData_ofFormat(x_176);
x_427 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_420, x_426, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_427;
}
case 2:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_428 = x_418;
} else {
 lean_dec_ref(x_418);
 x_428 = lean_box(0);
}
x_429 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_430 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_431 = 1;
x_432 = l_Lean_Name_toString(x_169, x_431);
if (lean_is_scalar(x_428)) {
 x_433 = lean_alloc_ctor(3, 1, 0);
} else {
 x_433 = x_428;
 lean_ctor_set_tag(x_433, 3);
}
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_433);
lean_ctor_set(x_184, 0, x_430);
x_434 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_434);
lean_ctor_set(x_176, 0, x_184);
x_435 = l_Lean_MessageData_ofFormat(x_176);
x_436 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_429, x_435, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_436;
}
case 4:
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_437 = x_418;
} else {
 lean_dec_ref(x_418);
 x_437 = lean_box(0);
}
x_438 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_439 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_440 = 1;
x_441 = l_Lean_Name_toString(x_169, x_440);
if (lean_is_scalar(x_437)) {
 x_442 = lean_alloc_ctor(3, 1, 0);
} else {
 x_442 = x_437;
 lean_ctor_set_tag(x_442, 3);
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_442);
lean_ctor_set(x_184, 0, x_439);
x_443 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_443);
lean_ctor_set(x_176, 0, x_184);
x_444 = l_Lean_MessageData_ofFormat(x_176);
x_445 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_438, x_444, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_445;
}
case 5:
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_446 = x_418;
} else {
 lean_dec_ref(x_418);
 x_446 = lean_box(0);
}
x_447 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_448 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_449 = 1;
x_450 = l_Lean_Name_toString(x_169, x_449);
if (lean_is_scalar(x_446)) {
 x_451 = lean_alloc_ctor(3, 1, 0);
} else {
 x_451 = x_446;
 lean_ctor_set_tag(x_451, 3);
}
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_451);
lean_ctor_set(x_184, 0, x_448);
x_452 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_452);
lean_ctor_set(x_176, 0, x_184);
x_453 = l_Lean_MessageData_ofFormat(x_176);
x_454 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_447, x_453, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_454;
}
case 6:
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_free_object(x_184);
lean_free_object(x_176);
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_455 = x_1;
} else {
 lean_dec_ref(x_1);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_418, 0);
lean_inc_ref(x_456);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_457 = x_418;
} else {
 lean_dec_ref(x_418);
 x_457 = lean_box(0);
}
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_456, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_456, 3);
lean_inc(x_460);
lean_dec_ref(x_456);
lean_inc(x_5);
lean_inc_ref(x_4);
x_461 = l_Lean_IR_nameToIRType(x_458, x_4, x_5, x_187);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; uint8_t x_464; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec_ref(x_461);
x_464 = l_Lean_IR_IRType_isScalar(x_462);
if (x_464 == 0)
{
lean_object* x_465; 
lean_dec(x_462);
lean_dec(x_459);
lean_dec(x_457);
lean_inc(x_5);
lean_inc_ref(x_4);
x_465 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_463);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_468 = x_465;
} else {
 lean_dec_ref(x_465);
 x_468 = lean_box(0);
}
x_472 = lean_ctor_get(x_466, 0);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_466, 1);
lean_inc_ref(x_473);
lean_dec(x_466);
x_474 = lean_array_get_size(x_174);
x_475 = l_Array_extract___redArg(x_174, x_460, x_474);
lean_dec(x_174);
x_491 = lean_array_get_size(x_475);
x_492 = lean_array_get_size(x_473);
x_493 = lean_nat_dec_eq(x_491, x_492);
lean_dec(x_491);
if (x_493 == 0)
{
lean_dec(x_492);
lean_dec_ref(x_475);
lean_dec_ref(x_473);
lean_dec_ref(x_472);
lean_dec(x_455);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_471;
}
else
{
if (x_464 == 0)
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
lean_dec(x_468);
x_494 = lean_unsigned_to_nat(0u);
x_495 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_496 = lean_nat_dec_lt(x_494, x_492);
if (x_496 == 0)
{
lean_dec(x_492);
x_476 = x_495;
x_477 = x_467;
goto block_490;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_497 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_498 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_473, x_497, x_475, x_492, x_495, x_494, x_467);
lean_dec(x_492);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec_ref(x_498);
x_476 = x_499;
x_477 = x_500;
goto block_490;
}
}
else
{
lean_dec(x_492);
lean_dec_ref(x_475);
lean_dec_ref(x_473);
lean_dec_ref(x_472);
lean_dec(x_455);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_471;
}
}
block_471:
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_box(12);
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_467);
return x_470;
}
block_490:
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_478 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_477);
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_481 = x_478;
} else {
 lean_dec_ref(x_478);
 x_481 = lean_box(0);
}
lean_inc(x_479);
x_482 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_472, x_473, x_475, x_479, x_3, x_4, x_5, x_480);
lean_dec_ref(x_475);
lean_dec_ref(x_473);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_485 = x_482;
} else {
 lean_dec_ref(x_482);
 x_485 = lean_box(0);
}
x_486 = l_Lean_IR_CtorInfo_type(x_472);
if (lean_is_scalar(x_481)) {
 x_487 = lean_alloc_ctor(0, 2, 0);
} else {
 x_487 = x_481;
}
lean_ctor_set(x_487, 0, x_472);
lean_ctor_set(x_487, 1, x_476);
if (lean_is_scalar(x_455)) {
 x_488 = lean_alloc_ctor(0, 4, 0);
} else {
 x_488 = x_455;
}
lean_ctor_set(x_488, 0, x_479);
lean_ctor_set(x_488, 1, x_486);
lean_ctor_set(x_488, 2, x_487);
lean_ctor_set(x_488, 3, x_483);
if (lean_is_scalar(x_485)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_485;
}
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_484);
return x_489;
}
else
{
lean_dec(x_481);
lean_dec(x_479);
lean_dec_ref(x_476);
lean_dec_ref(x_472);
lean_dec(x_455);
return x_482;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_460);
lean_dec(x_455);
lean_dec(x_174);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_501 = lean_ctor_get(x_465, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_465, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_503 = x_465;
} else {
 lean_dec_ref(x_465);
 x_503 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_503;
}
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_502);
return x_504;
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_460);
lean_dec(x_174);
lean_dec(x_169);
x_505 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_463);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec_ref(x_505);
x_508 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_511 = x_508;
} else {
 lean_dec_ref(x_508);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_512 = lean_alloc_ctor(0, 1, 0);
} else {
 x_512 = x_457;
 lean_ctor_set_tag(x_512, 0);
}
lean_ctor_set(x_512, 0, x_459);
x_513 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_513, 0, x_512);
if (lean_is_scalar(x_455)) {
 x_514 = lean_alloc_ctor(0, 4, 0);
} else {
 x_514 = x_455;
}
lean_ctor_set(x_514, 0, x_506);
lean_ctor_set(x_514, 1, x_462);
lean_ctor_set(x_514, 2, x_513);
lean_ctor_set(x_514, 3, x_509);
if (lean_is_scalar(x_511)) {
 x_515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_515 = x_511;
}
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_510);
return x_515;
}
else
{
lean_dec(x_506);
lean_dec(x_462);
lean_dec(x_459);
lean_dec(x_457);
lean_dec(x_455);
return x_508;
}
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_457);
lean_dec(x_455);
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_516 = lean_ctor_get(x_461, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_461, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_518 = x_461;
} else {
 lean_dec_ref(x_461);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(1, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
}
case 7:
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_520 = x_418;
} else {
 lean_dec_ref(x_418);
 x_520 = lean_box(0);
}
x_521 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_522 = 1;
x_523 = l_Lean_Name_toString(x_169, x_522);
if (lean_is_scalar(x_520)) {
 x_524 = lean_alloc_ctor(3, 1, 0);
} else {
 x_524 = x_520;
 lean_ctor_set_tag(x_524, 3);
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set_tag(x_184, 5);
lean_ctor_set(x_184, 1, x_524);
lean_ctor_set(x_184, 0, x_521);
x_525 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_525);
lean_ctor_set(x_176, 0, x_184);
x_526 = l_Lean_MessageData_ofFormat(x_176);
x_527 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_526, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_527;
}
default: 
{
lean_object* x_528; 
lean_dec(x_418);
lean_free_object(x_184);
lean_free_object(x_176);
x_528 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_174, x_3, x_4, x_5, x_187);
return x_528;
}
}
}
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; 
x_529 = lean_ctor_get(x_184, 0);
x_530 = lean_ctor_get(x_184, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_184);
x_531 = lean_ctor_get(x_529, 0);
lean_inc_ref(x_531);
lean_dec(x_529);
x_532 = 0;
lean_inc(x_169);
x_533 = l_Lean_Environment_find_x3f(x_531, x_169, x_532);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; 
lean_free_object(x_176);
lean_dec(x_174);
lean_dec(x_169);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_534 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_535 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_534, x_3, x_4, x_5, x_530);
return x_535;
}
else
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_533, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 x_537 = x_533;
} else {
 lean_dec_ref(x_533);
 x_537 = lean_box(0);
}
switch (lean_obj_tag(x_536)) {
case 0:
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_537);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_538 = x_536;
} else {
 lean_dec_ref(x_536);
 x_538 = lean_box(0);
}
x_539 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_540 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_541 = 1;
x_542 = l_Lean_Name_toString(x_169, x_541);
if (lean_is_scalar(x_538)) {
 x_543 = lean_alloc_ctor(3, 1, 0);
} else {
 x_543 = x_538;
 lean_ctor_set_tag(x_543, 3);
}
lean_ctor_set(x_543, 0, x_542);
x_544 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_544, 0, x_540);
lean_ctor_set(x_544, 1, x_543);
x_545 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_545);
lean_ctor_set(x_176, 0, x_544);
x_546 = l_Lean_MessageData_ofFormat(x_176);
x_547 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_539, x_546, x_4, x_5, x_530);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_547;
}
case 2:
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_537);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_548 = x_536;
} else {
 lean_dec_ref(x_536);
 x_548 = lean_box(0);
}
x_549 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_550 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_551 = 1;
x_552 = l_Lean_Name_toString(x_169, x_551);
if (lean_is_scalar(x_548)) {
 x_553 = lean_alloc_ctor(3, 1, 0);
} else {
 x_553 = x_548;
 lean_ctor_set_tag(x_553, 3);
}
lean_ctor_set(x_553, 0, x_552);
x_554 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_554, 0, x_550);
lean_ctor_set(x_554, 1, x_553);
x_555 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_555);
lean_ctor_set(x_176, 0, x_554);
x_556 = l_Lean_MessageData_ofFormat(x_176);
x_557 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_549, x_556, x_4, x_5, x_530);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_557;
}
case 4:
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_537);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_558 = x_536;
} else {
 lean_dec_ref(x_536);
 x_558 = lean_box(0);
}
x_559 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_560 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_561 = 1;
x_562 = l_Lean_Name_toString(x_169, x_561);
if (lean_is_scalar(x_558)) {
 x_563 = lean_alloc_ctor(3, 1, 0);
} else {
 x_563 = x_558;
 lean_ctor_set_tag(x_563, 3);
}
lean_ctor_set(x_563, 0, x_562);
x_564 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_564, 0, x_560);
lean_ctor_set(x_564, 1, x_563);
x_565 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_565);
lean_ctor_set(x_176, 0, x_564);
x_566 = l_Lean_MessageData_ofFormat(x_176);
x_567 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_559, x_566, x_4, x_5, x_530);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_567;
}
case 5:
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_537);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_568 = x_536;
} else {
 lean_dec_ref(x_536);
 x_568 = lean_box(0);
}
x_569 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_570 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_571 = 1;
x_572 = l_Lean_Name_toString(x_169, x_571);
if (lean_is_scalar(x_568)) {
 x_573 = lean_alloc_ctor(3, 1, 0);
} else {
 x_573 = x_568;
 lean_ctor_set_tag(x_573, 3);
}
lean_ctor_set(x_573, 0, x_572);
x_574 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_574, 0, x_570);
lean_ctor_set(x_574, 1, x_573);
x_575 = l_Lean_IR_ToIR_lowerLet___closed__11;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_575);
lean_ctor_set(x_176, 0, x_574);
x_576 = l_Lean_MessageData_ofFormat(x_176);
x_577 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_569, x_576, x_4, x_5, x_530);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_577;
}
case 6:
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_free_object(x_176);
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_578 = x_1;
} else {
 lean_dec_ref(x_1);
 x_578 = lean_box(0);
}
x_579 = lean_ctor_get(x_536, 0);
lean_inc_ref(x_579);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_580 = x_536;
} else {
 lean_dec_ref(x_536);
 x_580 = lean_box(0);
}
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_579, 2);
lean_inc(x_582);
x_583 = lean_ctor_get(x_579, 3);
lean_inc(x_583);
lean_dec_ref(x_579);
lean_inc(x_5);
lean_inc_ref(x_4);
x_584 = l_Lean_IR_nameToIRType(x_581, x_4, x_5, x_530);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec_ref(x_584);
x_587 = l_Lean_IR_IRType_isScalar(x_585);
if (x_587 == 0)
{
lean_object* x_588; 
lean_dec(x_585);
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_537);
lean_inc(x_5);
lean_inc_ref(x_4);
x_588 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_586);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_614; lean_object* x_615; uint8_t x_616; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_591 = x_588;
} else {
 lean_dec_ref(x_588);
 x_591 = lean_box(0);
}
x_595 = lean_ctor_get(x_589, 0);
lean_inc_ref(x_595);
x_596 = lean_ctor_get(x_589, 1);
lean_inc_ref(x_596);
lean_dec(x_589);
x_597 = lean_array_get_size(x_174);
x_598 = l_Array_extract___redArg(x_174, x_583, x_597);
lean_dec(x_174);
x_614 = lean_array_get_size(x_598);
x_615 = lean_array_get_size(x_596);
x_616 = lean_nat_dec_eq(x_614, x_615);
lean_dec(x_614);
if (x_616 == 0)
{
lean_dec(x_615);
lean_dec_ref(x_598);
lean_dec_ref(x_596);
lean_dec_ref(x_595);
lean_dec(x_578);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_594;
}
else
{
if (x_587 == 0)
{
lean_object* x_617; lean_object* x_618; uint8_t x_619; 
lean_dec(x_591);
x_617 = lean_unsigned_to_nat(0u);
x_618 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_619 = lean_nat_dec_lt(x_617, x_615);
if (x_619 == 0)
{
lean_dec(x_615);
x_599 = x_618;
x_600 = x_590;
goto block_613;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_620 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_621 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_596, x_620, x_598, x_615, x_618, x_617, x_590);
lean_dec(x_615);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec_ref(x_621);
x_599 = x_622;
x_600 = x_623;
goto block_613;
}
}
else
{
lean_dec(x_615);
lean_dec_ref(x_598);
lean_dec_ref(x_596);
lean_dec_ref(x_595);
lean_dec(x_578);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_594;
}
}
block_594:
{
lean_object* x_592; lean_object* x_593; 
x_592 = lean_box(12);
if (lean_is_scalar(x_591)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_591;
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_590);
return x_593;
}
block_613:
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_601 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_600);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_604 = x_601;
} else {
 lean_dec_ref(x_601);
 x_604 = lean_box(0);
}
lean_inc(x_602);
x_605 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_595, x_596, x_598, x_602, x_3, x_4, x_5, x_603);
lean_dec_ref(x_598);
lean_dec_ref(x_596);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_608 = x_605;
} else {
 lean_dec_ref(x_605);
 x_608 = lean_box(0);
}
x_609 = l_Lean_IR_CtorInfo_type(x_595);
if (lean_is_scalar(x_604)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_604;
}
lean_ctor_set(x_610, 0, x_595);
lean_ctor_set(x_610, 1, x_599);
if (lean_is_scalar(x_578)) {
 x_611 = lean_alloc_ctor(0, 4, 0);
} else {
 x_611 = x_578;
}
lean_ctor_set(x_611, 0, x_602);
lean_ctor_set(x_611, 1, x_609);
lean_ctor_set(x_611, 2, x_610);
lean_ctor_set(x_611, 3, x_606);
if (lean_is_scalar(x_608)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_608;
}
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_612, 1, x_607);
return x_612;
}
else
{
lean_dec(x_604);
lean_dec(x_602);
lean_dec_ref(x_599);
lean_dec_ref(x_595);
lean_dec(x_578);
return x_605;
}
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_583);
lean_dec(x_578);
lean_dec(x_174);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_624 = lean_ctor_get(x_588, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_588, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_626 = x_588;
} else {
 lean_dec_ref(x_588);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_625);
return x_627;
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_583);
lean_dec(x_174);
lean_dec(x_169);
x_628 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_586);
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
lean_dec_ref(x_628);
x_631 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_630);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_634 = x_631;
} else {
 lean_dec_ref(x_631);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_635 = lean_alloc_ctor(0, 1, 0);
} else {
 x_635 = x_580;
 lean_ctor_set_tag(x_635, 0);
}
lean_ctor_set(x_635, 0, x_582);
if (lean_is_scalar(x_537)) {
 x_636 = lean_alloc_ctor(11, 1, 0);
} else {
 x_636 = x_537;
 lean_ctor_set_tag(x_636, 11);
}
lean_ctor_set(x_636, 0, x_635);
if (lean_is_scalar(x_578)) {
 x_637 = lean_alloc_ctor(0, 4, 0);
} else {
 x_637 = x_578;
}
lean_ctor_set(x_637, 0, x_629);
lean_ctor_set(x_637, 1, x_585);
lean_ctor_set(x_637, 2, x_636);
lean_ctor_set(x_637, 3, x_632);
if (lean_is_scalar(x_634)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_634;
}
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_633);
return x_638;
}
else
{
lean_dec(x_629);
lean_dec(x_585);
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_578);
lean_dec(x_537);
return x_631;
}
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_578);
lean_dec(x_537);
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_639 = lean_ctor_get(x_584, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_584, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_641 = x_584;
} else {
 lean_dec_ref(x_584);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_640);
return x_642;
}
}
case 7:
{
lean_object* x_643; lean_object* x_644; uint8_t x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_537);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_643 = x_536;
} else {
 lean_dec_ref(x_536);
 x_643 = lean_box(0);
}
x_644 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_645 = 1;
x_646 = l_Lean_Name_toString(x_169, x_645);
if (lean_is_scalar(x_643)) {
 x_647 = lean_alloc_ctor(3, 1, 0);
} else {
 x_647 = x_643;
 lean_ctor_set_tag(x_647, 3);
}
lean_ctor_set(x_647, 0, x_646);
x_648 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_648, 0, x_644);
lean_ctor_set(x_648, 1, x_647);
x_649 = l_Lean_IR_ToIR_lowerLet___closed__16;
lean_ctor_set_tag(x_176, 5);
lean_ctor_set(x_176, 1, x_649);
lean_ctor_set(x_176, 0, x_648);
x_650 = l_Lean_MessageData_ofFormat(x_176);
x_651 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_650, x_4, x_5, x_530);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_651;
}
default: 
{
lean_object* x_652; 
lean_dec(x_537);
lean_dec(x_536);
lean_free_object(x_176);
x_652 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_174, x_3, x_4, x_5, x_530);
return x_652;
}
}
}
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_free_object(x_176);
x_653 = lean_ctor_get(x_182, 0);
lean_inc(x_653);
lean_dec_ref(x_182);
x_654 = lean_ctor_get(x_181, 1);
lean_inc(x_654);
lean_dec_ref(x_181);
x_655 = lean_ctor_get(x_653, 3);
lean_inc_ref(x_655);
lean_dec(x_653);
x_656 = lean_array_get_size(x_655);
lean_dec_ref(x_655);
x_657 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_169, x_656, x_174, x_3, x_4, x_5, x_654);
return x_657;
}
}
else
{
uint8_t x_658; 
lean_free_object(x_176);
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_658 = !lean_is_exclusive(x_181);
if (x_658 == 0)
{
return x_181;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_181, 0);
x_660 = lean_ctor_get(x_181, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_181);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
else
{
lean_object* x_662; lean_object* x_663; 
x_662 = lean_ctor_get(x_176, 1);
lean_inc(x_662);
lean_dec(x_176);
lean_inc(x_169);
x_663 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_169, x_5, x_662);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; uint8_t x_671; lean_object* x_672; 
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec_ref(x_663);
x_666 = lean_st_ref_get(x_5, x_665);
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 lean_ctor_release(x_666, 1);
 x_669 = x_666;
} else {
 lean_dec_ref(x_666);
 x_669 = lean_box(0);
}
x_670 = lean_ctor_get(x_667, 0);
lean_inc_ref(x_670);
lean_dec(x_667);
x_671 = 0;
lean_inc(x_169);
x_672 = l_Lean_Environment_find_x3f(x_670, x_169, x_671);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; lean_object* x_674; 
lean_dec(x_669);
lean_dec(x_174);
lean_dec(x_169);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_673 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_674 = l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_673, x_3, x_4, x_5, x_668);
return x_674;
}
else
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_672, 0);
lean_inc(x_675);
if (lean_is_exclusive(x_672)) {
 lean_ctor_release(x_672, 0);
 x_676 = x_672;
} else {
 lean_dec_ref(x_672);
 x_676 = lean_box(0);
}
switch (lean_obj_tag(x_675)) {
case 0:
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_dec(x_676);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 x_677 = x_675;
} else {
 lean_dec_ref(x_675);
 x_677 = lean_box(0);
}
x_678 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_679 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_680 = 1;
x_681 = l_Lean_Name_toString(x_169, x_680);
if (lean_is_scalar(x_677)) {
 x_682 = lean_alloc_ctor(3, 1, 0);
} else {
 x_682 = x_677;
 lean_ctor_set_tag(x_682, 3);
}
lean_ctor_set(x_682, 0, x_681);
if (lean_is_scalar(x_669)) {
 x_683 = lean_alloc_ctor(5, 2, 0);
} else {
 x_683 = x_669;
 lean_ctor_set_tag(x_683, 5);
}
lean_ctor_set(x_683, 0, x_679);
lean_ctor_set(x_683, 1, x_682);
x_684 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_685 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_685, 0, x_683);
lean_ctor_set(x_685, 1, x_684);
x_686 = l_Lean_MessageData_ofFormat(x_685);
x_687 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_678, x_686, x_4, x_5, x_668);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_687;
}
case 2:
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_676);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 x_688 = x_675;
} else {
 lean_dec_ref(x_675);
 x_688 = lean_box(0);
}
x_689 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_690 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_691 = 1;
x_692 = l_Lean_Name_toString(x_169, x_691);
if (lean_is_scalar(x_688)) {
 x_693 = lean_alloc_ctor(3, 1, 0);
} else {
 x_693 = x_688;
 lean_ctor_set_tag(x_693, 3);
}
lean_ctor_set(x_693, 0, x_692);
if (lean_is_scalar(x_669)) {
 x_694 = lean_alloc_ctor(5, 2, 0);
} else {
 x_694 = x_669;
 lean_ctor_set_tag(x_694, 5);
}
lean_ctor_set(x_694, 0, x_690);
lean_ctor_set(x_694, 1, x_693);
x_695 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_696 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
x_697 = l_Lean_MessageData_ofFormat(x_696);
x_698 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_689, x_697, x_4, x_5, x_668);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_698;
}
case 4:
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_676);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 x_699 = x_675;
} else {
 lean_dec_ref(x_675);
 x_699 = lean_box(0);
}
x_700 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_701 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_702 = 1;
x_703 = l_Lean_Name_toString(x_169, x_702);
if (lean_is_scalar(x_699)) {
 x_704 = lean_alloc_ctor(3, 1, 0);
} else {
 x_704 = x_699;
 lean_ctor_set_tag(x_704, 3);
}
lean_ctor_set(x_704, 0, x_703);
if (lean_is_scalar(x_669)) {
 x_705 = lean_alloc_ctor(5, 2, 0);
} else {
 x_705 = x_669;
 lean_ctor_set_tag(x_705, 5);
}
lean_ctor_set(x_705, 0, x_701);
lean_ctor_set(x_705, 1, x_704);
x_706 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_707 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
x_708 = l_Lean_MessageData_ofFormat(x_707);
x_709 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_700, x_708, x_4, x_5, x_668);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_709;
}
case 5:
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_676);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 x_710 = x_675;
} else {
 lean_dec_ref(x_675);
 x_710 = lean_box(0);
}
x_711 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_712 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_713 = 1;
x_714 = l_Lean_Name_toString(x_169, x_713);
if (lean_is_scalar(x_710)) {
 x_715 = lean_alloc_ctor(3, 1, 0);
} else {
 x_715 = x_710;
 lean_ctor_set_tag(x_715, 3);
}
lean_ctor_set(x_715, 0, x_714);
if (lean_is_scalar(x_669)) {
 x_716 = lean_alloc_ctor(5, 2, 0);
} else {
 x_716 = x_669;
 lean_ctor_set_tag(x_716, 5);
}
lean_ctor_set(x_716, 0, x_712);
lean_ctor_set(x_716, 1, x_715);
x_717 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_718 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
x_719 = l_Lean_MessageData_ofFormat(x_718);
x_720 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_711, x_719, x_4, x_5, x_668);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_720;
}
case 6:
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_dec(x_669);
lean_inc(x_168);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_721 = x_1;
} else {
 lean_dec_ref(x_1);
 x_721 = lean_box(0);
}
x_722 = lean_ctor_get(x_675, 0);
lean_inc_ref(x_722);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 x_723 = x_675;
} else {
 lean_dec_ref(x_675);
 x_723 = lean_box(0);
}
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
x_725 = lean_ctor_get(x_722, 2);
lean_inc(x_725);
x_726 = lean_ctor_get(x_722, 3);
lean_inc(x_726);
lean_dec_ref(x_722);
lean_inc(x_5);
lean_inc_ref(x_4);
x_727 = l_Lean_IR_nameToIRType(x_724, x_4, x_5, x_668);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; uint8_t x_730; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec_ref(x_727);
x_730 = l_Lean_IR_IRType_isScalar(x_728);
if (x_730 == 0)
{
lean_object* x_731; 
lean_dec(x_728);
lean_dec(x_725);
lean_dec(x_723);
lean_dec(x_676);
lean_inc(x_5);
lean_inc_ref(x_4);
x_731 = l_Lean_IR_getCtorLayout(x_169, x_4, x_5, x_729);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_757; lean_object* x_758; uint8_t x_759; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_734 = x_731;
} else {
 lean_dec_ref(x_731);
 x_734 = lean_box(0);
}
x_738 = lean_ctor_get(x_732, 0);
lean_inc_ref(x_738);
x_739 = lean_ctor_get(x_732, 1);
lean_inc_ref(x_739);
lean_dec(x_732);
x_740 = lean_array_get_size(x_174);
x_741 = l_Array_extract___redArg(x_174, x_726, x_740);
lean_dec(x_174);
x_757 = lean_array_get_size(x_741);
x_758 = lean_array_get_size(x_739);
x_759 = lean_nat_dec_eq(x_757, x_758);
lean_dec(x_757);
if (x_759 == 0)
{
lean_dec(x_758);
lean_dec_ref(x_741);
lean_dec_ref(x_739);
lean_dec_ref(x_738);
lean_dec(x_721);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_737;
}
else
{
if (x_730 == 0)
{
lean_object* x_760; lean_object* x_761; uint8_t x_762; 
lean_dec(x_734);
x_760 = lean_unsigned_to_nat(0u);
x_761 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_762 = lean_nat_dec_lt(x_760, x_758);
if (x_762 == 0)
{
lean_dec(x_758);
x_742 = x_761;
x_743 = x_733;
goto block_756;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_763 = l_Lean_IR_ToIR_getFVarValue___redArg___closed__0;
x_764 = l_Std_Rxo_Iterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_739, x_763, x_741, x_758, x_761, x_760, x_733);
lean_dec(x_758);
x_765 = lean_ctor_get(x_764, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_764, 1);
lean_inc(x_766);
lean_dec_ref(x_764);
x_742 = x_765;
x_743 = x_766;
goto block_756;
}
}
else
{
lean_dec(x_758);
lean_dec_ref(x_741);
lean_dec_ref(x_739);
lean_dec_ref(x_738);
lean_dec(x_721);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_737;
}
}
block_737:
{
lean_object* x_735; lean_object* x_736; 
x_735 = lean_box(12);
if (lean_is_scalar(x_734)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_734;
}
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_733);
return x_736;
}
block_756:
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_744 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_743);
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_744, 1);
lean_inc(x_746);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 lean_ctor_release(x_744, 1);
 x_747 = x_744;
} else {
 lean_dec_ref(x_744);
 x_747 = lean_box(0);
}
lean_inc(x_745);
x_748 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_738, x_739, x_741, x_745, x_3, x_4, x_5, x_746);
lean_dec_ref(x_741);
lean_dec_ref(x_739);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_751 = x_748;
} else {
 lean_dec_ref(x_748);
 x_751 = lean_box(0);
}
x_752 = l_Lean_IR_CtorInfo_type(x_738);
if (lean_is_scalar(x_747)) {
 x_753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_753 = x_747;
}
lean_ctor_set(x_753, 0, x_738);
lean_ctor_set(x_753, 1, x_742);
if (lean_is_scalar(x_721)) {
 x_754 = lean_alloc_ctor(0, 4, 0);
} else {
 x_754 = x_721;
}
lean_ctor_set(x_754, 0, x_745);
lean_ctor_set(x_754, 1, x_752);
lean_ctor_set(x_754, 2, x_753);
lean_ctor_set(x_754, 3, x_749);
if (lean_is_scalar(x_751)) {
 x_755 = lean_alloc_ctor(0, 2, 0);
} else {
 x_755 = x_751;
}
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_750);
return x_755;
}
else
{
lean_dec(x_747);
lean_dec(x_745);
lean_dec_ref(x_742);
lean_dec_ref(x_738);
lean_dec(x_721);
return x_748;
}
}
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_726);
lean_dec(x_721);
lean_dec(x_174);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_767 = lean_ctor_get(x_731, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_731, 1);
lean_inc(x_768);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_769 = x_731;
} else {
 lean_dec_ref(x_731);
 x_769 = lean_box(0);
}
if (lean_is_scalar(x_769)) {
 x_770 = lean_alloc_ctor(1, 2, 0);
} else {
 x_770 = x_769;
}
lean_ctor_set(x_770, 0, x_767);
lean_ctor_set(x_770, 1, x_768);
return x_770;
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_726);
lean_dec(x_174);
lean_dec(x_169);
x_771 = l_Lean_IR_ToIR_bindVar___redArg(x_168, x_3, x_729);
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec_ref(x_771);
x_774 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_773);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_777 = x_774;
} else {
 lean_dec_ref(x_774);
 x_777 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_778 = lean_alloc_ctor(0, 1, 0);
} else {
 x_778 = x_723;
 lean_ctor_set_tag(x_778, 0);
}
lean_ctor_set(x_778, 0, x_725);
if (lean_is_scalar(x_676)) {
 x_779 = lean_alloc_ctor(11, 1, 0);
} else {
 x_779 = x_676;
 lean_ctor_set_tag(x_779, 11);
}
lean_ctor_set(x_779, 0, x_778);
if (lean_is_scalar(x_721)) {
 x_780 = lean_alloc_ctor(0, 4, 0);
} else {
 x_780 = x_721;
}
lean_ctor_set(x_780, 0, x_772);
lean_ctor_set(x_780, 1, x_728);
lean_ctor_set(x_780, 2, x_779);
lean_ctor_set(x_780, 3, x_775);
if (lean_is_scalar(x_777)) {
 x_781 = lean_alloc_ctor(0, 2, 0);
} else {
 x_781 = x_777;
}
lean_ctor_set(x_781, 0, x_780);
lean_ctor_set(x_781, 1, x_776);
return x_781;
}
else
{
lean_dec(x_772);
lean_dec(x_728);
lean_dec(x_725);
lean_dec(x_723);
lean_dec(x_721);
lean_dec(x_676);
return x_774;
}
}
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_726);
lean_dec(x_725);
lean_dec(x_723);
lean_dec(x_721);
lean_dec(x_676);
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_782 = lean_ctor_get(x_727, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_727, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_784 = x_727;
} else {
 lean_dec_ref(x_727);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(1, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_782);
lean_ctor_set(x_785, 1, x_783);
return x_785;
}
}
case 7:
{
lean_object* x_786; lean_object* x_787; uint8_t x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_676);
lean_dec(x_174);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 x_786 = x_675;
} else {
 lean_dec_ref(x_675);
 x_786 = lean_box(0);
}
x_787 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_788 = 1;
x_789 = l_Lean_Name_toString(x_169, x_788);
if (lean_is_scalar(x_786)) {
 x_790 = lean_alloc_ctor(3, 1, 0);
} else {
 x_790 = x_786;
 lean_ctor_set_tag(x_790, 3);
}
lean_ctor_set(x_790, 0, x_789);
if (lean_is_scalar(x_669)) {
 x_791 = lean_alloc_ctor(5, 2, 0);
} else {
 x_791 = x_669;
 lean_ctor_set_tag(x_791, 5);
}
lean_ctor_set(x_791, 0, x_787);
lean_ctor_set(x_791, 1, x_790);
x_792 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_793 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
x_794 = l_Lean_MessageData_ofFormat(x_793);
x_795 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__3___redArg(x_794, x_4, x_5, x_668);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_795;
}
default: 
{
lean_object* x_796; 
lean_dec(x_676);
lean_dec(x_675);
lean_dec(x_669);
x_796 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_169, x_174, x_3, x_4, x_5, x_668);
return x_796;
}
}
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_797 = lean_ctor_get(x_664, 0);
lean_inc(x_797);
lean_dec_ref(x_664);
x_798 = lean_ctor_get(x_663, 1);
lean_inc(x_798);
lean_dec_ref(x_663);
x_799 = lean_ctor_get(x_797, 3);
lean_inc_ref(x_799);
lean_dec(x_797);
x_800 = lean_array_get_size(x_799);
lean_dec_ref(x_799);
x_801 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_169, x_800, x_174, x_3, x_4, x_5, x_798);
return x_801;
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_802 = lean_ctor_get(x_663, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_663, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_804 = x_663;
} else {
 lean_dec_ref(x_663);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(1, 2, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_802);
lean_ctor_set(x_805, 1, x_803);
return x_805;
}
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_806 = lean_ctor_get(x_176, 1);
lean_inc(x_806);
lean_dec_ref(x_176);
x_807 = lean_ctor_get(x_177, 0);
lean_inc(x_807);
lean_dec_ref(x_177);
x_808 = l_Lean_IR_Decl_params(x_807);
lean_dec(x_807);
x_809 = lean_array_get_size(x_808);
lean_dec_ref(x_808);
x_810 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_169, x_809, x_174, x_3, x_4, x_5, x_806);
return x_810;
}
}
default: 
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_14, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_812);
lean_dec_ref(x_14);
x_813 = l_Lean_IR_ToIR_getFVarValue___redArg(x_811, x_3, x_6);
lean_dec(x_811);
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; size_t x_817; size_t x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
lean_dec_ref(x_813);
x_816 = lean_ctor_get(x_814, 0);
lean_inc(x_816);
lean_dec_ref(x_814);
x_817 = lean_array_size(x_812);
x_818 = 0;
x_819 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___redArg(x_817, x_818, x_812, x_3, x_815);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec_ref(x_819);
x_822 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(x_1, x_2, x_816, x_820, x_3, x_4, x_5, x_821);
return x_822;
}
else
{
lean_object* x_823; lean_object* x_824; 
lean_dec_ref(x_812);
x_823 = lean_ctor_get(x_813, 1);
lean_inc(x_823);
lean_dec_ref(x_813);
x_824 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_823);
return x_824;
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
x_3 = lean_unsigned_to_nat(291u);
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
l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0 = _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0();
lean_mark_persistent(l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__0);
l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1 = _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1();
lean_mark_persistent(l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__1);
l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2 = _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2();
lean_mark_persistent(l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__2);
l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__3 = _init_l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__3();
lean_mark_persistent(l_panic___at_____private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___closed__3);
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
