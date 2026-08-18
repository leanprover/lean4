// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.BRecOn
// Imports: public import Lean.Util.HasConstCache public import Lean.Meta.PProdN public import Lean.Meta.Match.MatcherApp.Transform public import Lean.Elab.PreDefinition.Structural.Basic public import Lean.Elab.PreDefinition.Structural.RecArgInfo import Init.Data.Nat.Order import Init.Data.Order.Lemmas
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
lean_object* l_Lean_Expr_withAppAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_projM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
lean_object* l_Lean_Meta_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toBelow failed"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_searchPProd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PProd"};
static const lean_object* l_Lean_Elab_Structural_searchPProd___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_searchPProd___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_searchPProd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Structural_searchPProd___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_searchPProd___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Structural_searchPProd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_searchPProd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Elab_Structural_searchPProd___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_searchPProd___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Structural_searchPProd___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_searchPProd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 14, 124, 134, 125, 191, 184, 142)}};
static const lean_object* l_Lean_Elab_Structural_searchPProd___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_searchPProd___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Structural_searchPProd___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l_Lean_Elab_Structural_searchPProd___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_searchPProd___redArg___closed__4_value;
static const lean_string_object l_Lean_Elab_Structural_searchPProd___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Elab_Structural_searchPProd___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_searchPProd___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "belowDict not an app:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "belowDict step 2:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "belowDict step 1:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "belowDict start:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\narg:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "C"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 87, 66, 208, 34, 24, 101, 135)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_PProdN_packLambdas___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not type correct!"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "initial belowDict for "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "numMotives: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unexpected 'below' type"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "belowType: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_toBelow___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "searching IH for "};
static const lean_object* l_Lean_Elab_Structural_toBelow___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_toBelow___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_toBelow___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Structural_toBelow___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Elab_Structural_toBelow___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_toBelow___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_toBelow___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_toBelow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_toBelow___closed__0;
static lean_once_cell_t l_Lean_Elab_Structural_toBelow___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Structural_toBelow___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__3 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "insufficient number of parameters at recursive application "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "failed to eliminate recursive application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0_value;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "unexpected matcher application alternative"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\nat application"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "altNumParams: "};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", xs: "};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`matcherApp.addArg\?` failed"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "below before matcherApp.addArg: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.PreDefinition.Structural.Basic"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Elab.Structural.Positions.mapMwith"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: positions.size = ys.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: positions.numIndices = xs.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5;
static const lean_array_object l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_mkBRecOnConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_mkBRecOnConst___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_mkBRecOnConst___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_mkBRecOnConst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "brecOn is type incorrect"};
static const lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1;
static lean_once_cell_t l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2;
static lean_once_cell_t l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "mkBRecOnApp: Could not find "};
static const lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1);
v___x_56_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_55_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___boxed(lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(lean_object* v_00_u03b1_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_64_, v_a_65_, v_a_66_, v_a_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___boxed(lean_object* v_00_u03b1_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(v_00_u03b1_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(lean_object* v_00_u03b1_77_, lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___boxed(lean_object* v_00_u03b1_85_, lean_object* v_msg_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(v_00_u03b1_85_, v_msg_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg(lean_object* v_e_101_, lean_object* v_F_102_, lean_object* v_k_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; 
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
lean_inc_ref(v_e_101_);
v___x_109_ = lean_whnf(v_e_101_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v___x_109_, 1);
switch(lean_obj_tag(v_a_110_))
{
case 5:
{
lean_object* v_fn_111_; 
v_fn_111_ = lean_ctor_get(v_a_110_, 0);
lean_inc_ref(v_fn_111_);
if (lean_obj_tag(v_fn_111_) == 5)
{
lean_object* v_fn_112_; 
v_fn_112_ = lean_ctor_get(v_fn_111_, 0);
if (lean_obj_tag(v_fn_112_) == 4)
{
lean_object* v_declName_113_; 
v_declName_113_ = lean_ctor_get(v_fn_112_, 0);
lean_inc(v_declName_113_);
if (lean_obj_tag(v_declName_113_) == 1)
{
lean_object* v_pre_114_; 
v_pre_114_ = lean_ctor_get(v_declName_113_, 0);
if (lean_obj_tag(v_pre_114_) == 0)
{
lean_object* v_arg_115_; lean_object* v_arg_116_; lean_object* v_str_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_arg_115_ = lean_ctor_get(v_a_110_, 1);
lean_inc_ref(v_arg_115_);
lean_dec_ref_known(v_a_110_, 2);
v_arg_116_ = lean_ctor_get(v_fn_111_, 1);
lean_inc_ref(v_arg_116_);
lean_dec_ref_known(v_fn_111_, 2);
v_str_117_ = lean_ctor_get(v_declName_113_, 1);
lean_inc_ref(v_str_117_);
lean_dec_ref_known(v_declName_113_, 2);
v___x_118_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__0));
v___x_119_ = lean_string_dec_eq(v_str_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__1));
v___x_121_ = lean_string_dec_eq(v_str_117_, v___x_120_);
lean_dec_ref(v_str_117_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_115_);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_122_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_122_;
}
else
{
lean_object* v___x_123_; 
lean_dec_ref(v_e_101_);
v___x_123_ = l_Lean_Meta_saveState___redArg(v_a_105_, v_a_107_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v___x_123_, 1);
v___x_125_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__2));
v___x_126_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_102_);
v___x_127_ = l_Lean_Expr_proj___override(v___x_125_, v___x_126_, v_F_102_);
lean_inc_ref(v_k_103_);
v___x_128_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_116_, v___x_127_, v_k_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_dec(v_a_124_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
return v___x_128_;
}
else
{
lean_object* v_a_129_; uint8_t v___y_131_; uint8_t v___x_144_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
v___x_144_ = l_Lean_Exception_isInterrupt(v_a_129_);
if (v___x_144_ == 0)
{
uint8_t v___x_145_; 
v___x_145_ = l_Lean_Exception_isRuntime(v_a_129_);
v___y_131_ = v___x_145_;
goto v___jp_130_;
}
else
{
lean_dec(v_a_129_);
v___y_131_ = v___x_144_;
goto v___jp_130_;
}
v___jp_130_:
{
if (v___y_131_ == 0)
{
lean_object* v___x_132_; 
lean_dec_ref_known(v___x_128_, 1);
v___x_132_ = l_Lean_Meta_SavedState_restore___redArg(v_a_124_, v_a_105_, v_a_107_);
lean_dec(v_a_124_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec_ref_known(v___x_132_, 1);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = l_Lean_Expr_proj___override(v___x_125_, v___x_133_, v_F_102_);
v_e_101_ = v_arg_115_;
v_F_102_ = v___x_134_;
goto _start;
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
v_a_136_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_132_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_132_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
else
{
lean_dec(v_a_124_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
return v___x_128_;
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
v_a_146_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_123_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_123_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
else
{
lean_object* v___x_154_; 
lean_dec_ref(v_str_117_);
lean_dec_ref(v_e_101_);
v___x_154_ = l_Lean_Meta_saveState___redArg(v_a_105_, v_a_107_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__3));
v___x_157_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_102_);
v___x_158_ = l_Lean_Expr_proj___override(v___x_156_, v___x_157_, v_F_102_);
lean_inc_ref(v_k_103_);
v___x_159_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_116_, v___x_158_, v_k_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_dec(v_a_155_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
return v___x_159_;
}
else
{
lean_object* v_a_160_; uint8_t v___y_162_; uint8_t v___x_175_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
v___x_175_ = l_Lean_Exception_isInterrupt(v_a_160_);
if (v___x_175_ == 0)
{
uint8_t v___x_176_; 
v___x_176_ = l_Lean_Exception_isRuntime(v_a_160_);
v___y_162_ = v___x_176_;
goto v___jp_161_;
}
else
{
lean_dec(v_a_160_);
v___y_162_ = v___x_175_;
goto v___jp_161_;
}
v___jp_161_:
{
if (v___y_162_ == 0)
{
lean_object* v___x_163_; 
lean_dec_ref_known(v___x_159_, 1);
v___x_163_ = l_Lean_Meta_SavedState_restore___redArg(v_a_155_, v_a_105_, v_a_107_);
lean_dec(v_a_155_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec_ref_known(v___x_163_, 1);
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = l_Lean_Expr_proj___override(v___x_156_, v___x_164_, v_F_102_);
v_e_101_ = v_arg_115_;
v_F_102_ = v___x_165_;
goto _start;
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
v_a_167_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_163_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_163_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_dec(v_a_155_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
return v___x_159_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_115_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
v_a_177_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_154_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_154_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
else
{
lean_object* v___x_185_; 
lean_dec_ref_known(v_declName_113_, 2);
lean_dec_ref_known(v_fn_111_, 2);
lean_dec_ref_known(v_a_110_, 2);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_185_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_185_;
}
}
else
{
lean_object* v___x_186_; 
lean_dec(v_declName_113_);
lean_dec_ref_known(v_fn_111_, 2);
lean_dec_ref_known(v_a_110_, 2);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_186_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_186_;
}
}
else
{
lean_object* v___x_187_; 
lean_dec_ref_known(v_fn_111_, 2);
lean_dec_ref_known(v_a_110_, 2);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_187_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_187_;
}
}
else
{
lean_object* v___x_188_; 
lean_dec_ref_known(v_a_110_, 2);
lean_dec_ref(v_fn_111_);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_188_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_188_;
}
}
case 4:
{
lean_object* v_declName_189_; 
v_declName_189_ = lean_ctor_get(v_a_110_, 0);
lean_inc(v_declName_189_);
lean_dec_ref_known(v_a_110_, 2);
if (lean_obj_tag(v_declName_189_) == 1)
{
lean_object* v_pre_190_; 
v_pre_190_ = lean_ctor_get(v_declName_189_, 0);
if (lean_obj_tag(v_pre_190_) == 0)
{
lean_object* v_str_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_str_191_ = lean_ctor_get(v_declName_189_, 1);
lean_inc_ref(v_str_191_);
lean_dec_ref_known(v_declName_189_, 2);
v___x_192_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__4));
v___x_193_ = lean_string_dec_eq(v_str_191_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__5));
v___x_195_ = lean_string_dec_eq(v_str_191_, v___x_194_);
lean_dec_ref(v_str_191_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_196_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_196_;
}
else
{
lean_object* v___x_197_; 
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
lean_dec_ref(v_e_101_);
v___x_197_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_104_, v_a_105_, v_a_106_, v_a_107_);
return v___x_197_;
}
}
else
{
lean_object* v___x_198_; 
lean_dec_ref(v_str_191_);
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
lean_dec_ref(v_e_101_);
v___x_198_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_104_, v_a_105_, v_a_106_, v_a_107_);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec_ref_known(v_declName_189_, 2);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_199_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_199_;
}
}
else
{
lean_object* v___x_200_; 
lean_dec(v_declName_189_);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_200_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_200_;
}
}
default: 
{
lean_object* v___x_201_; 
lean_dec(v_a_110_);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
v___x_201_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_201_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_k_103_);
lean_dec_ref(v_F_102_);
lean_dec_ref(v_e_101_);
v_a_202_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_109_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_109_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg___boxed(lean_object* v_e_210_, lean_object* v_F_211_, lean_object* v_k_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_210_, v_F_211_, v_k_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd(lean_object* v_00_u03b1_219_, lean_object* v_e_220_, lean_object* v_F_221_, lean_object* v_k_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_220_, v_F_221_, v_k_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___boxed(lean_object* v_00_u03b1_229_, lean_object* v_e_230_, lean_object* v_F_231_, lean_object* v_k_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Elab_Structural_searchPProd(v_00_u03b1_229_, v_e_230_, v_F_231_, v_k_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(lean_object* v_k_239_, lean_object* v_b_240_, lean_object* v_c_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
v___x_247_ = lean_apply_7(v_k_239_, v_b_240_, v_c_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, lean_box(0));
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_248_, lean_object* v_b_249_, lean_object* v_c_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(v_k_248_, v_b_249_, v_c_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(lean_object* v_type_257_, lean_object* v_k_258_, uint8_t v_cleanupAnnotations_259_, uint8_t v_whnfType_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___f_266_; lean_object* v___x_267_; 
v___f_266_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_266_, 0, v_k_258_);
v___x_267_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_257_, v___f_266_, v_cleanupAnnotations_259_, v_whnfType_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v_a_276_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_267_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_267_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___boxed(lean_object* v_type_284_, lean_object* v_k_285_, lean_object* v_cleanupAnnotations_286_, lean_object* v_whnfType_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_293_; uint8_t v_whnfType_boxed_294_; lean_object* v_res_295_; 
v_cleanupAnnotations_boxed_293_ = lean_unbox(v_cleanupAnnotations_286_);
v_whnfType_boxed_294_ = lean_unbox(v_whnfType_287_);
v_res_295_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_284_, v_k_285_, v_cleanupAnnotations_boxed_293_, v_whnfType_boxed_294_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_object* v_00_u03b1_296_, lean_object* v_type_297_, lean_object* v_k_298_, uint8_t v_cleanupAnnotations_299_, uint8_t v_whnfType_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_297_, v_k_298_, v_cleanupAnnotations_299_, v_whnfType_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___boxed(lean_object* v_00_u03b1_307_, lean_object* v_type_308_, lean_object* v_k_309_, lean_object* v_cleanupAnnotations_310_, lean_object* v_whnfType_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_317_; uint8_t v_whnfType_boxed_318_; lean_object* v_res_319_; 
v_cleanupAnnotations_boxed_317_ = lean_unbox(v_cleanupAnnotations_310_);
v_whnfType_boxed_318_ = lean_unbox(v_whnfType_311_);
v_res_319_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_00_u03b1_307_, v_type_308_, v_k_309_, v_cleanupAnnotations_boxed_317_, v_whnfType_boxed_318_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(lean_object* v_cls_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_options_329_; uint8_t v_hasTrace_330_; 
v_options_329_ = lean_ctor_get(v___y_326_, 2);
v_hasTrace_330_ = lean_ctor_get_uint8(v_options_329_, sizeof(void*)*1);
if (v_hasTrace_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_cls_323_);
v___x_331_ = lean_box(v_hasTrace_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
else
{
lean_object* v_inheritedTraceOptions_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_inheritedTraceOptions_333_ = lean_ctor_get(v___y_326_, 13);
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_335_ = l_Lean_Name_append(v___x_334_, v_cls_323_);
v___x_336_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_333_, v_options_329_, v___x_335_);
lean_dec(v___x_335_);
v___x_337_ = lean_box(v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed(lean_object* v_cls_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_345_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0(void){
_start:
{
lean_object* v___x_346_; double v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_float_of_nat(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(lean_object* v_cls_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_ref_358_; lean_object* v___x_359_; lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_404_; 
v_ref_358_ = lean_ctor_get(v___y_355_, 5);
v___x_359_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_404_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_404_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_404_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v_traceState_365_; lean_object* v_env_366_; lean_object* v_nextMacroScope_367_; lean_object* v_ngen_368_; lean_object* v_auxDeclNGen_369_; lean_object* v_cache_370_; lean_object* v_messages_371_; lean_object* v_infoState_372_; lean_object* v_snapshotTasks_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_403_; 
v___x_364_ = lean_st_ref_take(v___y_356_);
v_traceState_365_ = lean_ctor_get(v___x_364_, 4);
v_env_366_ = lean_ctor_get(v___x_364_, 0);
v_nextMacroScope_367_ = lean_ctor_get(v___x_364_, 1);
v_ngen_368_ = lean_ctor_get(v___x_364_, 2);
v_auxDeclNGen_369_ = lean_ctor_get(v___x_364_, 3);
v_cache_370_ = lean_ctor_get(v___x_364_, 5);
v_messages_371_ = lean_ctor_get(v___x_364_, 6);
v_infoState_372_ = lean_ctor_get(v___x_364_, 7);
v_snapshotTasks_373_ = lean_ctor_get(v___x_364_, 8);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_403_ == 0)
{
v___x_375_ = v___x_364_;
v_isShared_376_ = v_isSharedCheck_403_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_snapshotTasks_373_);
lean_inc(v_infoState_372_);
lean_inc(v_messages_371_);
lean_inc(v_cache_370_);
lean_inc(v_traceState_365_);
lean_inc(v_auxDeclNGen_369_);
lean_inc(v_ngen_368_);
lean_inc(v_nextMacroScope_367_);
lean_inc(v_env_366_);
lean_dec(v___x_364_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_403_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
uint64_t v_tid_377_; lean_object* v_traces_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_402_; 
v_tid_377_ = lean_ctor_get_uint64(v_traceState_365_, sizeof(void*)*1);
v_traces_378_ = lean_ctor_get(v_traceState_365_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_traceState_365_);
if (v_isSharedCheck_402_ == 0)
{
v___x_380_ = v_traceState_365_;
v_isShared_381_ = v_isSharedCheck_402_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_traces_378_);
lean_dec(v_traceState_365_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_402_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; double v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_382_ = lean_box(0);
v___x_383_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_384_ = 0;
v___x_385_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_386_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_386_, 0, v_cls_351_);
lean_ctor_set(v___x_386_, 1, v___x_382_);
lean_ctor_set(v___x_386_, 2, v___x_385_);
lean_ctor_set_float(v___x_386_, sizeof(void*)*3, v___x_383_);
lean_ctor_set_float(v___x_386_, sizeof(void*)*3 + 8, v___x_383_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*3 + 16, v___x_384_);
v___x_387_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_388_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v_a_360_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
lean_inc(v_ref_358_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_ref_358_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_PersistentArray_push___redArg(v_traces_378_, v___x_389_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_390_);
v___x_392_ = v___x_380_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_390_);
lean_ctor_set_uint64(v_reuseFailAlloc_401_, sizeof(void*)*1, v_tid_377_);
v___x_392_ = v_reuseFailAlloc_401_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 4, v___x_392_);
v___x_394_ = v___x_375_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_env_366_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_nextMacroScope_367_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_ngen_368_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v_auxDeclNGen_369_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_400_, 5, v_cache_370_);
lean_ctor_set(v_reuseFailAlloc_400_, 6, v_messages_371_);
lean_ctor_set(v_reuseFailAlloc_400_, 7, v_infoState_372_);
lean_ctor_set(v_reuseFailAlloc_400_, 8, v_snapshotTasks_373_);
v___x_394_ = v_reuseFailAlloc_400_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = lean_st_ref_put(v___y_356_, v___x_394_);
v___x_396_ = lean_box(0);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_396_);
v___x_398_ = v___x_362_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object* v_cls_405_, lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_405_, v_msg_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_412_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v___f_419_, lean_object* v_a_420_, lean_object* v_C_421_, lean_object* v_cls_422_, lean_object* v_belowDict_423_, lean_object* v_F_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___x_502_; 
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc(v___y_426_);
lean_inc_ref(v___y_425_);
v___x_502_ = lean_apply_5(v___f_419_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, lean_box(0));
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; uint8_t v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = lean_unbox(v_a_503_);
lean_dec(v_a_503_);
if (v___x_504_ == 0)
{
v___y_464_ = v___y_425_;
v___y_465_ = v___y_426_;
v___y_466_ = v___y_427_;
v___y_467_ = v___y_428_;
goto v___jp_463_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_423_);
v___x_506_ = l_Lean_indentExpr(v_belowDict_423_);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_inc(v_cls_422_);
v___x_508_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_422_, v___x_507_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_dec_ref_known(v___x_508_, 1);
v___y_464_ = v___y_425_;
v___y_465_ = v___y_426_;
v___y_466_ = v___y_427_;
v___y_467_ = v___y_428_;
goto v___jp_463_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_F_424_);
lean_dec_ref(v_belowDict_423_);
lean_dec(v_cls_422_);
lean_dec_ref(v_a_420_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_F_424_);
lean_dec_ref(v_belowDict_423_);
lean_dec(v_cls_422_);
lean_dec_ref(v_a_420_);
v_a_517_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_502_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_502_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
v___jp_430_:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_isExprDefEq(v___y_431_, v_a_420_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_454_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_454_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_454_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_454_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint8_t v___x_441_; 
v___x_441_ = lean_unbox(v_a_437_);
lean_dec(v_a_437_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_del_object(v___x_439_);
lean_dec_ref(v_F_424_);
v___x_442_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_432_, v___y_433_, v___y_434_, v___y_435_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v___x_452_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_F_424_);
v___x_452_ = v___x_439_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_F_424_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v_F_424_);
v_a_455_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_436_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_436_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
v___jp_463_:
{
if (lean_obj_tag(v_belowDict_423_) == 5)
{
lean_object* v_fn_468_; lean_object* v_arg_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
lean_dec(v_cls_422_);
v_fn_468_ = lean_ctor_get(v_belowDict_423_, 0);
lean_inc_ref(v_fn_468_);
v_arg_469_ = lean_ctor_get(v_belowDict_423_, 1);
lean_inc_ref(v_arg_469_);
lean_dec_ref_known(v_belowDict_423_, 2);
v___x_470_ = l_Lean_Expr_getAppFn(v_fn_468_);
lean_dec_ref(v_fn_468_);
v___x_471_ = lean_expr_eqv(v___x_470_, v_C_421_);
lean_dec_ref(v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec_ref(v_arg_469_);
lean_dec_ref(v_F_424_);
lean_dec_ref(v_a_420_);
v___x_472_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_464_, v___y_465_, v___y_466_, v___y_467_);
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
else
{
v___y_431_ = v_arg_469_;
v___y_432_ = v___y_464_;
v___y_433_ = v___y_465_;
v___y_434_ = v___y_466_;
v___y_435_ = v___y_467_;
goto v___jp_430_;
}
}
else
{
lean_object* v_options_481_; uint8_t v_hasTrace_482_; 
lean_dec_ref(v_F_424_);
lean_dec_ref(v_a_420_);
v_options_481_ = lean_ctor_get(v___y_466_, 2);
v_hasTrace_482_ = lean_ctor_get_uint8(v_options_481_, sizeof(void*)*1);
if (v_hasTrace_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v_belowDict_423_);
lean_dec(v_cls_422_);
v___x_483_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v___x_483_;
}
else
{
lean_object* v_inheritedTraceOptions_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_inheritedTraceOptions_484_ = lean_ctor_get(v___y_466_, 13);
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_422_);
v___x_486_ = l_Lean_Name_append(v___x_485_, v_cls_422_);
v___x_487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_484_, v_options_481_, v___x_486_);
lean_dec(v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec_ref(v_belowDict_423_);
lean_dec(v_cls_422_);
v___x_488_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_490_ = l_Lean_indentExpr(v_belowDict_423_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_422_, v___x_491_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v___x_493_; 
lean_dec_ref_known(v___x_492_, 1);
v___x_493_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v___x_493_;
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_492_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_492_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v___f_525_, lean_object* v_a_526_, lean_object* v_C_527_, lean_object* v_cls_528_, lean_object* v_belowDict_529_, lean_object* v_F_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v___f_525_, v_a_526_, v_C_527_, v_cls_528_, v_belowDict_529_, v_F_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v_C_527_);
return v_res_536_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0(void){
_start:
{
lean_object* v___x_537_; lean_object* v_dummy_538_; 
v___x_537_ = lean_box(0);
v_dummy_538_ = l_Lean_Expr_sort___override(v___x_537_);
return v_dummy_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_539_, lean_object* v___f_540_, lean_object* v_C_541_, lean_object* v_cls_542_, lean_object* v_F_543_, lean_object* v_xs_544_, lean_object* v_belowDict_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint8_t v___x_551_; lean_object* v___x_552_; 
v___x_551_ = 1;
v___x_552_ = l_Lean_Meta_zetaReduce(v_arg_539_, v___x_551_, v___x_551_, v___x_551_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___f_554_; lean_object* v_dummy_555_; lean_object* v_nargs_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc_n(v_a_553_, 2);
lean_dec_ref_known(v___x_552_, 1);
v___f_554_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed), 11, 4);
lean_closure_set(v___f_554_, 0, v___f_540_);
lean_closure_set(v___f_554_, 1, v_a_553_);
lean_closure_set(v___f_554_, 2, v_C_541_);
lean_closure_set(v___f_554_, 3, v_cls_542_);
v_dummy_555_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_556_ = l_Lean_Expr_getAppNumArgs(v_a_553_);
lean_inc(v_nargs_556_);
v___x_557_ = lean_mk_array(v_nargs_556_, v_dummy_555_);
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_sub(v_nargs_556_, v___x_558_);
lean_dec(v_nargs_556_);
v___x_560_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_553_, v___x_557_, v___x_559_);
v___x_573_ = lean_array_get_size(v_xs_544_);
v___x_574_ = lean_array_get_size(v___x_560_);
v___x_575_ = lean_nat_dec_le(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v___x_560_);
lean_dec_ref(v___f_554_);
lean_dec_ref(v_F_543_);
v___x_576_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_546_, v___y_547_, v___y_548_, v___y_549_);
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
v___y_562_ = v___y_546_;
v___y_563_ = v___y_547_;
v___y_564_ = v___y_548_;
v___y_565_ = v___y_549_;
goto v___jp_561_;
}
v___jp_561_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_566_ = lean_array_get_size(v___x_560_);
v___x_567_ = lean_array_get_size(v_xs_544_);
v___x_568_ = lean_nat_sub(v___x_566_, v___x_567_);
v___x_569_ = l_Array_extract___redArg(v___x_560_, v___x_568_, v___x_566_);
lean_dec_ref(v___x_560_);
v___x_570_ = l_Lean_Expr_replaceFVars(v_belowDict_545_, v_xs_544_, v___x_569_);
v___x_571_ = l_Lean_mkAppN(v_F_543_, v___x_569_);
lean_dec_ref(v___x_569_);
v___x_572_ = l_Lean_Elab_Structural_searchPProd___redArg(v___x_570_, v___x_571_, v___f_554_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_572_;
}
}
else
{
lean_dec_ref(v_F_543_);
lean_dec(v_cls_542_);
lean_dec_ref(v_C_541_);
lean_dec_ref(v___f_540_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_585_, lean_object* v___f_586_, lean_object* v_C_587_, lean_object* v_cls_588_, lean_object* v_F_589_, lean_object* v_xs_590_, lean_object* v_belowDict_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_585_, v___f_586_, v_C_587_, v_cls_588_, v_F_589_, v_xs_590_, v_belowDict_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_belowDict_591_);
lean_dec_ref(v_xs_590_);
return v_res_597_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0));
v___x_600_ = l_Lean_stringToMessageData(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v___f_601_, lean_object* v_arg_602_, lean_object* v_C_603_, lean_object* v_cls_604_, lean_object* v_belowDict_605_, lean_object* v_F_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
lean_inc_ref(v___f_601_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
v___x_612_ = lean_apply_5(v___f_601_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, lean_box(0));
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___f_614_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; uint8_t v___x_622_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
lean_inc(v_cls_604_);
v___f_614_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_614_, 0, v_arg_602_);
lean_closure_set(v___f_614_, 1, v___f_601_);
lean_closure_set(v___f_614_, 2, v_C_603_);
lean_closure_set(v___f_614_, 3, v_cls_604_);
lean_closure_set(v___f_614_, 4, v_F_606_);
v___x_622_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
if (v___x_622_ == 0)
{
lean_dec(v_cls_604_);
v___y_616_ = v___y_607_;
v___y_617_ = v___y_608_;
v___y_618_ = v___y_609_;
v___y_619_ = v___y_610_;
goto v___jp_615_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_605_);
v___x_624_ = l_Lean_indentExpr(v_belowDict_605_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_604_, v___x_625_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec_ref_known(v___x_626_, 1);
v___y_616_ = v___y_607_;
v___y_617_ = v___y_608_;
v___y_618_ = v___y_609_;
v___y_619_ = v___y_610_;
goto v___jp_615_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v___f_614_);
lean_dec_ref(v_belowDict_605_);
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
v___jp_615_:
{
uint8_t v___x_620_; lean_object* v___x_621_; 
v___x_620_ = 0;
v___x_621_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_605_, v___f_614_, v___x_620_, v___x_620_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
return v___x_621_;
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_F_606_);
lean_dec_ref(v_belowDict_605_);
lean_dec(v_cls_604_);
lean_dec_ref(v_C_603_);
lean_dec_ref(v_arg_602_);
lean_dec_ref(v___f_601_);
v_a_635_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_612_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_612_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v___f_643_, lean_object* v_arg_644_, lean_object* v_C_645_, lean_object* v_cls_646_, lean_object* v_belowDict_647_, lean_object* v_F_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v___f_643_, v_arg_644_, v_C_645_, v_cls_646_, v_belowDict_647_, v_F_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_654_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_666_ = l_Lean_stringToMessageData(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_669_ = l_Lean_stringToMessageData(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_670_, lean_object* v_belowDict_671_, lean_object* v_arg_672_, lean_object* v_F_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_cls_679_; lean_object* v___f_680_; lean_object* v___x_681_; lean_object* v_a_682_; lean_object* v___f_683_; uint8_t v___x_684_; 
v_cls_679_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_680_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
v___x_681_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_679_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v___x_681_);
lean_inc_ref(v_arg_672_);
v___f_683_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_683_, 0, v___f_680_);
lean_closure_set(v___f_683_, 1, v_arg_672_);
lean_closure_set(v___f_683_, 2, v_C_670_);
lean_closure_set(v___f_683_, 3, v_cls_679_);
v___x_684_ = lean_unbox(v_a_682_);
lean_dec(v_a_682_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec_ref(v_arg_672_);
v___x_685_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_671_, v_F_673_, v___f_683_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_686_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_671_);
v___x_687_ = l_Lean_indentExpr(v_belowDict_671_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Lean_indentExpr(v_arg_672_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_679_, v___x_692_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v___x_694_; 
lean_dec_ref_known(v___x_693_, 1);
v___x_694_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_671_, v_F_673_, v___f_683_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
return v___x_694_;
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v___f_683_);
lean_dec_ref(v_F_673_);
lean_dec_ref(v_belowDict_671_);
v_a_695_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_693_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_693_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_703_, lean_object* v_belowDict_704_, lean_object* v_arg_705_, lean_object* v_F_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_703_, v_belowDict_704_, v_arg_705_, v_F_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v___x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_options_719_; uint8_t v_hasTrace_720_; 
v_options_719_ = lean_ctor_get(v___y_716_, 2);
v_hasTrace_720_ = lean_ctor_get_uint8(v_options_719_, sizeof(void*)*1);
if (v_hasTrace_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec(v___x_713_);
v___x_721_ = lean_box(v_hasTrace_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
else
{
lean_object* v_inheritedTraceOptions_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_inheritedTraceOptions_723_ = lean_ctor_get(v___y_716_, 13);
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_725_ = l_Lean_Name_append(v___x_724_, v___x_713_);
v___x_726_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_723_, v_options_719_, v___x_725_);
lean_dec(v___x_725_);
v___x_727_ = lean_box(v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v___x_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_736_, lean_object* v_x_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_t_736_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_744_, lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_744_, v_x_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec_ref(v_x_745_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v_t_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__1));
v___x_762_ = l_Lean_Core_mkFreshUserName(v___x_761_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_772_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_772_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_772_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_772_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___f_767_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_767_, 0, v_t_755_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_a_763_);
lean_ctor_set(v___x_768_, 1, v___f_767_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_t_755_);
v_a_773_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_762_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_762_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v_t_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v_t_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_788_, lean_object* v_a_789_, lean_object* v_x_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_array_set(v___y_791_, v_a_789_, v___x_788_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_800_, v_a_801_, v_x_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v_a_801_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_810_, lean_object* v_a_811_, lean_object* v_x_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_snd_819_; lean_object* v_fst_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_871_; 
v_snd_819_ = lean_ctor_get(v___y_813_, 1);
v_fst_820_ = lean_ctor_get(v___y_813_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___y_813_);
if (v_isSharedCheck_871_ == 0)
{
v___x_822_ = v___y_813_;
v_isShared_823_ = v_isSharedCheck_871_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snd_819_);
lean_inc(v_fst_820_);
lean_dec(v___y_813_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_871_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_array_824_; lean_object* v_start_825_; lean_object* v_stop_826_; uint8_t v___x_827_; 
v_array_824_ = lean_ctor_get(v_snd_819_, 0);
v_start_825_ = lean_ctor_get(v_snd_819_, 1);
v_stop_826_ = lean_ctor_get(v_snd_819_, 2);
v___x_827_ = lean_nat_dec_lt(v_start_825_, v_stop_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_829_; 
lean_dec_ref(v_a_811_);
lean_dec_ref(v___x_810_);
if (v_isShared_823_ == 0)
{
v___x_829_ = v___x_822_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_fst_820_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_snd_819_);
v___x_829_ = v_reuseFailAlloc_832_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
else
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_867_; 
lean_inc(v_stop_826_);
lean_inc(v_start_825_);
lean_inc_ref(v_array_824_);
v_isSharedCheck_867_ = !lean_is_exclusive(v_snd_819_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; lean_object* v_unused_869_; lean_object* v_unused_870_; 
v_unused_868_ = lean_ctor_get(v_snd_819_, 2);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_snd_819_, 1);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_snd_819_, 0);
lean_dec(v_unused_870_);
v___x_834_ = v_snd_819_;
v_isShared_835_ = v_isSharedCheck_867_;
goto v_resetjp_833_;
}
else
{
lean_dec(v_snd_819_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_867_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___f_837_; size_t v_sz_838_; size_t v___x_839_; lean_object* v___x_8719__overap_840_; lean_object* v___x_841_; 
v___x_836_ = lean_array_fget_borrowed(v_array_824_, v_start_825_);
lean_inc(v___x_836_);
v___f_837_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_837_, 0, v___x_836_);
v_sz_838_ = lean_array_size(v_a_811_);
v___x_839_ = ((size_t)0ULL);
v___x_8719__overap_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_810_, v_a_811_, v___f_837_, v_sz_838_, v___x_839_, v_fst_820_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
v___x_841_ = lean_apply_5(v___x_8719__overap_840_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, lean_box(0));
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_858_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_858_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_858_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_858_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_add(v_start_825_, v___x_846_);
lean_dec(v_start_825_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_847_);
v___x_849_ = v___x_834_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_array_824_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_stop_826_);
v___x_849_ = v_reuseFailAlloc_857_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_849_);
lean_ctor_set(v___x_822_, 0, v_a_842_);
v___x_851_ = v___x_822_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_842_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_849_);
v___x_851_ = v_reuseFailAlloc_856_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_852_);
v___x_854_ = v___x_844_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_del_object(v___x_834_);
lean_dec(v_stop_826_);
lean_dec(v_start_825_);
lean_dec_ref(v_array_824_);
lean_del_object(v___x_822_);
v_a_859_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_841_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_841_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_872_, lean_object* v_a_873_, lean_object* v_x_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_872_, v_a_873_, v_x_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__8));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_895_, lean_object* v___x_896_, lean_object* v_positions_897_, lean_object* v_a_898_, lean_object* v___f_899_, lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v_k_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___f_905_, lean_object* v___x_906_, lean_object* v_Cs_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_8747__overap_914_; lean_object* v___x_915_; 
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_907_);
lean_inc_ref(v___x_895_);
v___x_8747__overap_914_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_895_, v___x_896_, v___x_913_, v_positions_897_, v_a_898_, v_Cs_907_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
v___x_915_ = lean_apply_5(v___x_8747__overap_914_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, lean_box(0));
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
v___x_917_ = lean_apply_5(v___f_899_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, lean_box(0));
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; uint8_t v___x_966_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = l_Lean_mkAppN(v___x_900_, v_a_916_);
lean_dec(v_a_916_);
v___x_920_ = l_Subarray_copy___redArg(v___x_901_);
v___x_921_ = l_Lean_mkAppN(v___x_919_, v___x_920_);
lean_dec_ref(v___x_920_);
v___x_966_ = lean_unbox(v_a_918_);
lean_dec(v_a_918_);
if (v___x_966_ == 0)
{
v___y_923_ = v___y_908_;
v___y_924_ = v___y_909_;
v___y_925_ = v___y_910_;
v___y_926_ = v___y_911_;
goto v___jp_922_;
}
else
{
lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_toMonadRef_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_8809__overap_985_; lean_object* v___x_986_; 
v___f_967_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_968_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_969_ = l_Lean_Core_instMonadQuotationCoreM;
lean_inc(v___x_904_);
v___x_970_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_968_, v___x_904_, v___x_969_);
lean_inc(v___f_905_);
v___x_971_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_967_, v___f_905_, v___x_970_);
v_toMonadRef_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc_ref(v_toMonadRef_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_974_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6);
lean_inc_ref(v_Cs_907_);
v___x_975_ = lean_array_to_list(v_Cs_907_);
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7));
v___x_977_ = lean_box(0);
v___x_978_ = l_List_mapTR_loop___redArg(v___x_976_, v___x_975_, v___x_977_);
v___x_979_ = l_Lean_MessageData_ofList(v___x_978_);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_974_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
lean_inc_ref(v___x_921_);
v___x_983_ = l_Lean_indentExpr(v___x_921_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
lean_inc(v___x_903_);
lean_inc_ref(v___x_906_);
lean_inc_ref(v___x_895_);
v___x_8809__overap_985_ = l_Lean_addTrace___redArg(v___x_895_, v___x_906_, v_toMonadRef_972_, v___x_973_, v___x_903_, v___x_984_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
v___x_986_ = lean_apply_5(v___x_8809__overap_985_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, lean_box(0));
if (lean_obj_tag(v___x_986_) == 0)
{
lean_dec_ref_known(v___x_986_, 1);
v___y_923_ = v___y_908_;
v___y_924_ = v___y_909_;
v___y_925_ = v___y_910_;
v___y_926_ = v___y_911_;
goto v___jp_922_;
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v___x_921_);
lean_dec_ref(v_Cs_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v_k_902_);
lean_dec_ref(v___x_895_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
v___jp_922_:
{
lean_object* v___x_927_; 
lean_inc_ref(v___x_921_);
v___x_927_ = l_Lean_Meta_isTypeCorrect(v___x_921_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; uint8_t v___x_929_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_929_ = lean_unbox(v_a_928_);
lean_dec(v_a_928_);
if (v___x_929_ == 0)
{
lean_object* v_options_930_; uint8_t v_hasTrace_931_; 
v_options_930_ = lean_ctor_get(v___y_925_, 2);
v_hasTrace_931_ = lean_ctor_get_uint8(v_options_930_, sizeof(void*)*1);
if (v_hasTrace_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref(v___x_906_);
lean_dec(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v___x_895_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
v___x_932_ = lean_apply_7(v_k_902_, v_Cs_907_, v___x_921_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, lean_box(0));
return v___x_932_;
}
else
{
lean_object* v_inheritedTraceOptions_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_inheritedTraceOptions_933_ = lean_ctor_get(v___y_925_, 13);
v___x_934_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_903_);
v___x_935_ = l_Lean_Name_append(v___x_934_, v___x_903_);
v___x_936_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_933_, v_options_930_, v___x_935_);
lean_dec(v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
lean_dec_ref(v___x_906_);
lean_dec(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v___x_895_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
v___x_937_ = lean_apply_7(v_k_902_, v_Cs_907_, v___x_921_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, lean_box(0));
return v___x_937_;
}
else
{
lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_toMonadRef_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_8779__overap_946_; lean_object* v___x_947_; 
v___f_938_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_939_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_940_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_941_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_939_, v___x_904_, v___x_940_);
v___x_942_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_938_, v___f_905_, v___x_941_);
v_toMonadRef_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc_ref(v_toMonadRef_943_);
lean_dec_ref(v___x_942_);
v___x_944_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_945_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
v___x_8779__overap_946_ = l_Lean_addTrace___redArg(v___x_895_, v___x_906_, v_toMonadRef_943_, v___x_944_, v___x_903_, v___x_945_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
v___x_947_ = lean_apply_5(v___x_8779__overap_946_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, lean_box(0));
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v___x_948_; 
lean_dec_ref_known(v___x_947_, 1);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
v___x_948_ = lean_apply_7(v_k_902_, v_Cs_907_, v___x_921_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, lean_box(0));
return v___x_948_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v___x_921_);
lean_dec_ref(v_Cs_907_);
lean_dec_ref(v_k_902_);
v_a_949_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_947_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_947_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
else
{
lean_object* v___x_957_; 
lean_dec_ref(v___x_906_);
lean_dec(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v___x_895_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
v___x_957_ = lean_apply_7(v_k_902_, v_Cs_907_, v___x_921_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, lean_box(0));
return v___x_957_;
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v___x_921_);
lean_dec_ref(v_Cs_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v_k_902_);
lean_dec_ref(v___x_895_);
v_a_958_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_927_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_927_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_a_916_);
lean_dec_ref(v_Cs_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v_k_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___x_895_);
v_a_995_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_917_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_917_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_Cs_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v_k_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v___f_899_);
lean_dec_ref(v___x_895_);
v_a_1003_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_915_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_915_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_1011_ = _args[0];
lean_object* v___x_1012_ = _args[1];
lean_object* v_positions_1013_ = _args[2];
lean_object* v_a_1014_ = _args[3];
lean_object* v___f_1015_ = _args[4];
lean_object* v___x_1016_ = _args[5];
lean_object* v___x_1017_ = _args[6];
lean_object* v_k_1018_ = _args[7];
lean_object* v___x_1019_ = _args[8];
lean_object* v___x_1020_ = _args[9];
lean_object* v___f_1021_ = _args[10];
lean_object* v___x_1022_ = _args[11];
lean_object* v_Cs_1023_ = _args[12];
lean_object* v___y_1024_ = _args[13];
lean_object* v___y_1025_ = _args[14];
lean_object* v___y_1026_ = _args[15];
lean_object* v___y_1027_ = _args[16];
lean_object* v___y_1028_ = _args[17];
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_1011_, v___x_1012_, v_positions_1013_, v_a_1014_, v___f_1015_, v___x_1016_, v___x_1017_, v_k_1018_, v___x_1019_, v___x_1020_, v___f_1021_, v___x_1022_, v_Cs_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1029_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_unsigned_to_nat(37u);
v___x_1031_ = l_Lean_Level_ofNat(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1033_ = l_Lean_Expr_sort___override(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1040_, lean_object* v___x_1041_, lean_object* v___f_1042_, lean_object* v___f_1043_, lean_object* v___x_1044_, lean_object* v_numTypeFormers_1045_, lean_object* v___f_1046_, lean_object* v___x_1047_, lean_object* v_k_1048_, lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v___f_1051_, lean_object* v___x_1052_, lean_object* v_numIndParams_1053_, lean_object* v_a_1054_, lean_object* v_f_1055_, lean_object* v_args_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_nat_add(v_numIndParams_1053_, v_numTypeFormers_1045_);
v___x_1196_ = lean_array_get_size(v_args_1056_);
v___x_1197_ = lean_nat_dec_lt(v___x_1195_, v___x_1196_);
lean_dec(v___x_1195_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v_args_1056_);
lean_dec_ref(v_f_1055_);
lean_dec(v_numIndParams_1053_);
lean_dec_ref(v_k_1048_);
lean_dec_ref(v___x_1047_);
lean_dec(v_numTypeFormers_1045_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v___f_1042_);
lean_dec_ref(v_positions_1040_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
v___x_1198_ = lean_apply_5(v___f_1046_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; uint8_t v___x_1200_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = lean_unbox(v_a_1199_);
lean_dec(v_a_1199_);
if (v___x_1200_ == 0)
{
lean_dec_ref(v_a_1054_);
lean_dec_ref(v___x_1052_);
lean_dec(v___f_1051_);
lean_dec(v___x_1050_);
lean_dec(v___x_1049_);
lean_dec_ref(v___x_1041_);
v___y_1182_ = v___y_1057_;
v___y_1183_ = v___y_1058_;
v___y_1184_ = v___y_1059_;
v___y_1185_ = v___y_1060_;
goto v___jp_1181_;
}
else
{
lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_toMonadRef_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_8954__overap_1211_; lean_object* v___x_1212_; 
v___f_1201_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_1202_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_1203_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1204_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1202_, v___x_1050_, v___x_1203_);
v___x_1205_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1201_, v___f_1051_, v___x_1204_);
v_toMonadRef_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc_ref(v_toMonadRef_1206_);
lean_dec_ref(v___x_1205_);
v___x_1207_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1208_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1209_ = l_Lean_indentExpr(v_a_1054_);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_8954__overap_1211_ = l_Lean_addTrace___redArg(v___x_1041_, v___x_1052_, v_toMonadRef_1206_, v___x_1207_, v___x_1049_, v___x_1210_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
v___x_1212_ = lean_apply_5(v___x_8954__overap_1211_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_dec_ref_known(v___x_1212_, 1);
v___y_1182_ = v___y_1057_;
v___y_1183_ = v___y_1058_;
v___y_1184_ = v___y_1059_;
v___y_1185_ = v___y_1060_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_a_1054_);
lean_dec_ref(v___x_1052_);
lean_dec(v___f_1051_);
lean_dec(v___x_1050_);
lean_dec(v___x_1049_);
lean_dec_ref(v___x_1041_);
v_a_1221_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1198_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1198_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_dec_ref(v_a_1054_);
v___y_1170_ = v___y_1057_;
v___y_1171_ = v___y_1058_;
v___y_1172_ = v___y_1059_;
v___y_1173_ = v___y_1060_;
goto v___jp_1169_;
}
v___jp_1062_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; size_t v_sz_1076_; size_t v___x_1077_; lean_object* v___x_8855__overap_1078_; lean_object* v___x_1079_; 
v___x_1071_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1072_ = lean_mk_array(v___y_1063_, v___x_1071_);
v___x_1073_ = lean_array_get_size(v___y_1065_);
v___x_1074_ = l_Array_toSubarray___redArg(v___y_1065_, v___y_1064_, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1072_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v_sz_1076_ = lean_array_size(v_positions_1040_);
v___x_1077_ = ((size_t)0ULL);
lean_inc_ref(v___x_1041_);
v___x_8855__overap_1078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1041_, v_positions_1040_, v___f_1042_, v_sz_1076_, v___x_1077_, v___x_1075_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
v___x_1079_ = lean_apply_5(v___x_8855__overap_1078_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, lean_box(0));
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v_fst_1081_; size_t v_sz_1082_; lean_object* v___x_8858__overap_1083_; lean_object* v___x_1084_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v_fst_1081_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_fst_1081_);
lean_dec(v_a_1080_);
v_sz_1082_ = lean_array_size(v_fst_1081_);
lean_inc_ref(v___x_1041_);
v___x_8858__overap_1083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1041_, v___f_1043_, v_sz_1082_, v___x_1077_, v_fst_1081_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
v___x_1084_ = lean_apply_5(v___x_8858__overap_1083_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, lean_box(0));
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; uint8_t v___x_1086_; lean_object* v___x_8862__overap_1087_; lean_object* v___x_1088_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = 0;
v___x_8862__overap_1087_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1044_, v___x_1041_, v_a_1085_, v___y_1066_, v___x_1086_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
v___x_1088_ = lean_apply_5(v___x_8862__overap_1087_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, lean_box(0));
return v___x_1088_;
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v___y_1066_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v___x_1041_);
v_a_1089_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1084_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1084_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___y_1066_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v___x_1041_);
v_a_1097_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1079_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1079_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
v___jp_1105_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = l_Subarray_copy___redArg(v___y_1106_);
v___x_1114_ = l_Lean_mkAppN(v_f_1055_, v___x_1113_);
lean_dec_ref(v___x_1113_);
lean_inc_ref(v___x_1114_);
v___x_1115_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1045_, v___x_1114_, v___y_1107_, v___y_1110_, v___y_1111_, v___y_1108_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
lean_inc_ref(v___f_1046_);
lean_inc(v___y_1108_);
lean_inc_ref(v___y_1111_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1107_);
v___x_1117_ = lean_apply_5(v___f_1046_, v___y_1107_, v___y_1110_, v___y_1111_, v___y_1108_, lean_box(0));
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_lower_1119_; lean_object* v_upper_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1152_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v_lower_1119_ = lean_ctor_get(v___y_1112_, 0);
v_upper_1120_ = lean_ctor_get(v___y_1112_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___y_1112_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1122_ = v___y_1112_;
v_isShared_1123_ = v_isSharedCheck_1152_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_upper_1120_);
lean_inc(v_lower_1119_);
lean_dec(v___y_1112_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1152_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1124_ = l_Array_toSubarray___redArg(v_args_1056_, v_lower_1119_, v_upper_1120_);
lean_inc_ref(v___x_1052_);
lean_inc(v___f_1051_);
lean_inc(v___x_1050_);
lean_inc(v___x_1049_);
lean_inc(v_a_1116_);
lean_inc_ref(v_positions_1040_);
lean_inc_ref(v___x_1041_);
v___f_1125_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1125_, 0, v___x_1041_);
lean_closure_set(v___f_1125_, 1, v___x_1047_);
lean_closure_set(v___f_1125_, 2, v_positions_1040_);
lean_closure_set(v___f_1125_, 3, v_a_1116_);
lean_closure_set(v___f_1125_, 4, v___f_1046_);
lean_closure_set(v___f_1125_, 5, v___x_1114_);
lean_closure_set(v___f_1125_, 6, v___x_1124_);
lean_closure_set(v___f_1125_, 7, v_k_1048_);
lean_closure_set(v___f_1125_, 8, v___x_1049_);
lean_closure_set(v___f_1125_, 9, v___x_1050_);
lean_closure_set(v___f_1125_, 10, v___f_1051_);
lean_closure_set(v___f_1125_, 11, v___x_1052_);
v___x_1126_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1040_);
v___x_1127_ = lean_unbox(v_a_1118_);
lean_dec(v_a_1118_);
if (v___x_1127_ == 0)
{
lean_del_object(v___x_1122_);
lean_dec_ref(v___x_1052_);
lean_dec(v___f_1051_);
lean_dec(v___x_1050_);
lean_dec(v___x_1049_);
v___y_1063_ = v___x_1126_;
v___y_1064_ = v___y_1109_;
v___y_1065_ = v_a_1116_;
v___y_1066_ = v___f_1125_;
v___y_1067_ = v___y_1107_;
v___y_1068_ = v___y_1110_;
v___y_1069_ = v___y_1111_;
v___y_1070_ = v___y_1108_;
goto v___jp_1062_;
}
else
{
lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_toMonadRef_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___f_1128_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_1129_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_1130_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1131_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1129_, v___x_1050_, v___x_1130_);
v___x_1132_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1128_, v___f_1051_, v___x_1131_);
v_toMonadRef_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_toMonadRef_1133_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1135_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1126_);
v___x_1136_ = l_Nat_reprFast(v___x_1126_);
v___x_1137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
v___x_1138_ = l_Lean_MessageData_ofFormat(v___x_1137_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 7);
lean_ctor_set(v___x_1122_, 1, v___x_1138_);
lean_ctor_set(v___x_1122_, 0, v___x_1135_);
v___x_1140_ = v___x_1122_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_8901__overap_1141_; lean_object* v___x_1142_; 
lean_inc_ref(v___x_1041_);
v___x_8901__overap_1141_ = l_Lean_addTrace___redArg(v___x_1041_, v___x_1052_, v_toMonadRef_1133_, v___x_1134_, v___x_1049_, v___x_1140_);
lean_inc(v___y_1108_);
lean_inc_ref(v___y_1111_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1107_);
v___x_1142_ = lean_apply_5(v___x_8901__overap_1141_, v___y_1107_, v___y_1110_, v___y_1111_, v___y_1108_, lean_box(0));
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref_known(v___x_1142_, 1);
v___y_1063_ = v___x_1126_;
v___y_1064_ = v___y_1109_;
v___y_1065_ = v_a_1116_;
v___y_1066_ = v___f_1125_;
v___y_1067_ = v___y_1107_;
v___y_1068_ = v___y_1110_;
v___y_1069_ = v___y_1111_;
v___y_1070_ = v___y_1108_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v___x_1126_);
lean_dec_ref(v___f_1125_);
lean_dec(v_a_1116_);
lean_dec(v___y_1109_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v___f_1042_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_positions_1040_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_a_1116_);
lean_dec_ref(v___x_1114_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1109_);
lean_dec_ref(v_args_1056_);
lean_dec_ref(v___x_1052_);
lean_dec(v___f_1051_);
lean_dec(v___x_1050_);
lean_dec(v___x_1049_);
lean_dec_ref(v_k_1048_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v___f_1046_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v___f_1042_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_positions_1040_);
v_a_1153_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1117_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1117_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v___x_1114_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1109_);
lean_dec_ref(v_args_1056_);
lean_dec_ref(v___x_1052_);
lean_dec(v___f_1051_);
lean_dec(v___x_1050_);
lean_dec(v___x_1049_);
lean_dec_ref(v_k_1048_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v___f_1046_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v___f_1042_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_positions_1040_);
v_a_1161_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1115_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1115_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
v___jp_1169_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1053_);
lean_inc_ref(v_args_1056_);
v___x_1175_ = l_Array_toSubarray___redArg(v_args_1056_, v___x_1174_, v_numIndParams_1053_);
v___x_1176_ = lean_nat_add(v_numIndParams_1053_, v_numTypeFormers_1045_);
lean_dec(v_numIndParams_1053_);
v___x_1177_ = lean_array_get_size(v_args_1056_);
v___x_1178_ = lean_nat_dec_le(v___x_1176_, v___x_1174_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1176_);
lean_ctor_set(v___x_1179_, 1, v___x_1177_);
v___y_1106_ = v___x_1175_;
v___y_1107_ = v___y_1170_;
v___y_1108_ = v___y_1173_;
v___y_1109_ = v___x_1174_;
v___y_1110_ = v___y_1171_;
v___y_1111_ = v___y_1172_;
v___y_1112_ = v___x_1179_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v___x_1176_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1174_);
lean_ctor_set(v___x_1180_, 1, v___x_1177_);
v___y_1106_ = v___x_1175_;
v___y_1107_ = v___y_1170_;
v___y_1108_ = v___y_1173_;
v___y_1109_ = v___x_1174_;
v___y_1110_ = v___y_1171_;
v___y_1111_ = v___y_1172_;
v___y_1112_ = v___x_1180_;
goto v___jp_1105_;
}
}
v___jp_1181_:
{
lean_object* v___x_1186_; lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v___x_1186_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1229_ = _args[0];
lean_object* v___x_1230_ = _args[1];
lean_object* v___f_1231_ = _args[2];
lean_object* v___f_1232_ = _args[3];
lean_object* v___x_1233_ = _args[4];
lean_object* v_numTypeFormers_1234_ = _args[5];
lean_object* v___f_1235_ = _args[6];
lean_object* v___x_1236_ = _args[7];
lean_object* v_k_1237_ = _args[8];
lean_object* v___x_1238_ = _args[9];
lean_object* v___x_1239_ = _args[10];
lean_object* v___f_1240_ = _args[11];
lean_object* v___x_1241_ = _args[12];
lean_object* v_numIndParams_1242_ = _args[13];
lean_object* v_a_1243_ = _args[14];
lean_object* v_f_1244_ = _args[15];
lean_object* v_args_1245_ = _args[16];
lean_object* v___y_1246_ = _args[17];
lean_object* v___y_1247_ = _args[18];
lean_object* v___y_1248_ = _args[19];
lean_object* v___y_1249_ = _args[20];
lean_object* v___y_1250_ = _args[21];
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1229_, v___x_1230_, v___f_1231_, v___f_1232_, v___x_1233_, v_numTypeFormers_1234_, v___f_1235_, v___x_1236_, v_k_1237_, v___x_1238_, v___x_1239_, v___f_1240_, v___x_1241_, v_numIndParams_1242_, v_a_1243_, v_f_1244_, v_args_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
return v_res_1251_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_instMonadEIO(lean_box(0));
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1254_ = l_StateRefT_x27_instMonad___redArg(v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1263_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1262_, v___x_1261_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1265_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1266_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1265_, v___x_1264_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1270_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1272_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_1273_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1272_, v___x_1271_, v___x_1270_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___f_1275_; lean_object* v___f_1276_; lean_object* v___x_1277_; 
v___x_1274_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1275_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1276_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_1277_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1276_, v___f_1275_, v___x_1274_);
return v___x_1277_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1281_, lean_object* v_numIndParams_1282_, lean_object* v_positions_1283_, lean_object* v_k_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v_toApplicative_1291_; lean_object* v_toFunctor_1292_; lean_object* v_toSeq_1293_; lean_object* v_toSeqLeft_1294_; lean_object* v_toSeqRight_1295_; lean_object* v___f_1296_; lean_object* v___f_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_toApplicative_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1434_; 
v___x_1290_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1291_ = lean_ctor_get(v___x_1290_, 0);
v_toFunctor_1292_ = lean_ctor_get(v_toApplicative_1291_, 0);
v_toSeq_1293_ = lean_ctor_get(v_toApplicative_1291_, 2);
v_toSeqLeft_1294_ = lean_ctor_get(v_toApplicative_1291_, 3);
v_toSeqRight_1295_ = lean_ctor_get(v_toApplicative_1291_, 4);
v___f_1296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1297_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1292_, 2);
v___f_1298_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1298_, 0, v_toFunctor_1292_);
v___f_1299_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1299_, 0, v_toFunctor_1292_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___f_1298_);
lean_ctor_set(v___x_1300_, 1, v___f_1299_);
lean_inc(v_toSeqRight_1295_);
v___f_1301_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1301_, 0, v_toSeqRight_1295_);
lean_inc(v_toSeqLeft_1294_);
v___f_1302_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1302_, 0, v_toSeqLeft_1294_);
lean_inc(v_toSeq_1293_);
v___f_1303_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1303_, 0, v_toSeq_1293_);
v___x_1304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1300_);
lean_ctor_set(v___x_1304_, 1, v___f_1296_);
lean_ctor_set(v___x_1304_, 2, v___f_1303_);
lean_ctor_set(v___x_1304_, 3, v___f_1302_);
lean_ctor_set(v___x_1304_, 4, v___f_1301_);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___f_1297_);
v___x_1306_ = l_StateRefT_x27_instMonad___redArg(v___x_1305_);
v_toApplicative_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v___x_1306_, 1);
lean_dec(v_unused_1435_);
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1434_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_toApplicative_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1434_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_toFunctor_1311_; lean_object* v_toSeq_1312_; lean_object* v_toSeqLeft_1313_; lean_object* v_toSeqRight_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1432_; 
v_toFunctor_1311_ = lean_ctor_get(v_toApplicative_1307_, 0);
v_toSeq_1312_ = lean_ctor_get(v_toApplicative_1307_, 2);
v_toSeqLeft_1313_ = lean_ctor_get(v_toApplicative_1307_, 3);
v_toSeqRight_1314_ = lean_ctor_get(v_toApplicative_1307_, 4);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_toApplicative_1307_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v_toApplicative_1307_, 1);
lean_dec(v_unused_1433_);
v___x_1316_ = v_toApplicative_1307_;
v_isShared_1317_ = v_isSharedCheck_1432_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_toSeqRight_1314_);
lean_inc(v_toSeqLeft_1313_);
lean_inc(v_toSeq_1312_);
lean_inc(v_toFunctor_1311_);
lean_dec(v_toApplicative_1307_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1432_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___f_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v___f_1323_; lean_object* v___f_1324_; lean_object* v___f_1325_; lean_object* v___x_1327_; 
v___f_1318_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1319_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1311_);
v___f_1320_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1320_, 0, v_toFunctor_1311_);
v___f_1321_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1321_, 0, v_toFunctor_1311_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___f_1320_);
lean_ctor_set(v___x_1322_, 1, v___f_1321_);
v___f_1323_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1323_, 0, v_toSeqRight_1314_);
v___f_1324_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1324_, 0, v_toSeqLeft_1313_);
v___f_1325_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1325_, 0, v_toSeq_1312_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v___f_1323_);
lean_ctor_set(v___x_1316_, 3, v___f_1324_);
lean_ctor_set(v___x_1316_, 2, v___f_1325_);
lean_ctor_set(v___x_1316_, 1, v___f_1318_);
lean_ctor_set(v___x_1316_, 0, v___x_1322_);
v___x_1327_ = v___x_1316_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___f_1318_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v___f_1325_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v___f_1324_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v___f_1323_);
v___x_1327_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v___f_1319_);
lean_ctor_set(v___x_1309_, 0, v___x_1327_);
v___x_1329_ = v___x_1309_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___f_1319_);
v___x_1329_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___f_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_toApplicative_1333_; lean_object* v_toFunctor_1334_; lean_object* v_toSeq_1335_; lean_object* v_toSeqLeft_1336_; lean_object* v_toSeqRight_1337_; lean_object* v___f_1338_; lean_object* v___f_1339_; lean_object* v___x_1340_; lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___f_1330_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1332_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1333_ = lean_ctor_get(v___x_1290_, 0);
v_toFunctor_1334_ = lean_ctor_get(v_toApplicative_1333_, 0);
v_toSeq_1335_ = lean_ctor_get(v_toApplicative_1333_, 2);
v_toSeqLeft_1336_ = lean_ctor_get(v_toApplicative_1333_, 3);
v_toSeqRight_1337_ = lean_ctor_get(v_toApplicative_1333_, 4);
lean_inc_ref_n(v_toFunctor_1334_, 2);
v___f_1338_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1338_, 0, v_toFunctor_1334_);
v___f_1339_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1339_, 0, v_toFunctor_1334_);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___f_1338_);
lean_ctor_set(v___x_1340_, 1, v___f_1339_);
lean_inc(v_toSeqRight_1337_);
v___f_1341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1341_, 0, v_toSeqRight_1337_);
lean_inc(v_toSeqLeft_1336_);
v___f_1342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1342_, 0, v_toSeqLeft_1336_);
lean_inc(v_toSeq_1335_);
v___f_1343_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1343_, 0, v_toSeq_1335_);
v___x_1344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1340_);
lean_ctor_set(v___x_1344_, 1, v___f_1296_);
lean_ctor_set(v___x_1344_, 2, v___f_1343_);
lean_ctor_set(v___x_1344_, 3, v___f_1342_);
lean_ctor_set(v___x_1344_, 4, v___f_1341_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___f_1297_);
v___x_1346_ = l_StateRefT_x27_instMonad___redArg(v___x_1345_);
v___x_1347_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1347_, 0, lean_box(0));
lean_closure_set(v___x_1347_, 1, lean_box(0));
lean_closure_set(v___x_1347_, 2, v___x_1346_);
v___x_1348_ = l_instMonadControlTOfPure___redArg(v___x_1347_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_a_1286_);
lean_inc_ref(v_a_1285_);
lean_inc_ref(v_below_1281_);
v___x_1349_ = lean_infer_type(v_below_1281_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v_a_1354_; lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___x_1357_; lean_object* v_numTypeFormers_1358_; lean_object* v___f_1359_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; uint8_t v___x_1405_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_n(v_a_1350_, 2);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1352_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1353_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1351_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref(v___x_1353_);
v___f_1355_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
lean_inc_ref_n(v___x_1329_, 2);
v___f_1356_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed), 9, 1);
lean_closure_set(v___f_1356_, 0, v___x_1329_);
v___x_1357_ = l_Lean_instInhabitedExpr;
v_numTypeFormers_1358_ = lean_array_get_size(v_positions_1283_);
v___f_1359_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1359_, 0, v_positions_1283_);
lean_closure_set(v___f_1359_, 1, v___x_1329_);
lean_closure_set(v___f_1359_, 2, v___f_1356_);
lean_closure_set(v___f_1359_, 3, v___f_1355_);
lean_closure_set(v___f_1359_, 4, v___x_1348_);
lean_closure_set(v___f_1359_, 5, v_numTypeFormers_1358_);
lean_closure_set(v___f_1359_, 6, v___f_1352_);
lean_closure_set(v___f_1359_, 7, v___x_1357_);
lean_closure_set(v___f_1359_, 8, v_k_1284_);
lean_closure_set(v___f_1359_, 9, v___x_1351_);
lean_closure_set(v___f_1359_, 10, v___x_1331_);
lean_closure_set(v___f_1359_, 11, v___f_1330_);
lean_closure_set(v___f_1359_, 12, v___x_1332_);
lean_closure_set(v___f_1359_, 13, v_numIndParams_1282_);
lean_closure_set(v___f_1359_, 14, v_a_1350_);
v___x_1405_ = lean_unbox(v_a_1354_);
lean_dec(v_a_1354_);
if (v___x_1405_ == 0)
{
v___y_1373_ = v_a_1285_;
v___y_1374_ = v_a_1286_;
v___y_1375_ = v_a_1287_;
v___y_1376_ = v_a_1288_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1406_; lean_object* v_toMonadRef_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_8528__overap_1412_; lean_object* v___x_1413_; 
v___x_1406_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1407_ = lean_ctor_get(v___x_1406_, 0);
v___x_1408_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1409_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15);
lean_inc(v_a_1350_);
v___x_1410_ = l_Lean_MessageData_ofExpr(v_a_1350_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1409_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
lean_inc_ref(v_toMonadRef_1407_);
lean_inc_ref(v___x_1329_);
v___x_8528__overap_1412_ = l_Lean_addTrace___redArg(v___x_1329_, v___x_1332_, v_toMonadRef_1407_, v___x_1408_, v___x_1351_, v___x_1411_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_a_1286_);
lean_inc_ref(v_a_1285_);
v___x_1413_ = lean_apply_5(v___x_8528__overap_1412_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, lean_box(0));
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_dec_ref_known(v___x_1413_, 1);
v___y_1373_ = v_a_1285_;
v___y_1374_ = v_a_1286_;
v___y_1375_ = v_a_1287_;
v___y_1376_ = v_a_1288_;
goto v___jp_1372_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v___f_1359_);
lean_dec(v_a_1350_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v_below_1281_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
v___jp_1360_:
{
lean_object* v_dummy_1365_; lean_object* v_nargs_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_8194__overap_1370_; lean_object* v___x_1371_; 
v_dummy_1365_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1366_ = l_Lean_Expr_getAppNumArgs(v_a_1350_);
lean_inc(v_nargs_1366_);
v___x_1367_ = lean_mk_array(v_nargs_1366_, v_dummy_1365_);
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_sub(v_nargs_1366_, v___x_1368_);
lean_dec(v_nargs_1366_);
v___x_8194__overap_1370_ = l_Lean_Expr_withAppAux___redArg(v___f_1359_, v_a_1350_, v___x_1367_, v___x_1369_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
v___x_1371_ = lean_apply_5(v___x_8194__overap_1370_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, lean_box(0));
return v___x_1371_;
}
v___jp_1372_:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_Meta_isTypeCorrect(v_below_1281_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; uint8_t v___x_1379_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = lean_unbox(v_a_1378_);
lean_dec(v_a_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v_a_1381_; uint8_t v___x_1382_; 
v___x_1380_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1351_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = lean_unbox(v_a_1381_);
lean_dec(v_a_1381_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v___x_1329_);
v___y_1361_ = v___y_1373_;
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1376_;
goto v___jp_1360_;
}
else
{
lean_object* v___x_1383_; lean_object* v_toMonadRef_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_8506__overap_1387_; lean_object* v___x_1388_; 
v___x_1383_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1384_ = lean_ctor_get(v___x_1383_, 0);
v___x_1385_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1386_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_toMonadRef_1384_);
v___x_8506__overap_1387_ = l_Lean_addTrace___redArg(v___x_1329_, v___x_1332_, v_toMonadRef_1384_, v___x_1385_, v___x_1351_, v___x_1386_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
v___x_1388_ = lean_apply_5(v___x_8506__overap_1387_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, lean_box(0));
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_dec_ref_known(v___x_1388_, 1);
v___y_1361_ = v___y_1373_;
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1376_;
goto v___jp_1360_;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v___f_1359_);
lean_dec(v_a_1350_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1329_);
v___y_1361_ = v___y_1373_;
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1376_;
goto v___jp_1360_;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v___f_1359_);
lean_dec(v_a_1350_);
lean_dec_ref(v___x_1329_);
v_a_1397_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1377_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1377_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v___x_1348_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v_k_1284_);
lean_dec_ref(v_positions_1283_);
lean_dec(v_numIndParams_1282_);
lean_dec_ref(v_below_1281_);
v_a_1422_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1349_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1349_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1436_, lean_object* v_numIndParams_1437_, lean_object* v_positions_1438_, lean_object* v_k_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1436_, v_numIndParams_1437_, v_positions_1438_, v_k_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1446_, lean_object* v_inst_1447_, lean_object* v_below_1448_, lean_object* v_numIndParams_1449_, lean_object* v_positions_1450_, lean_object* v_k_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1448_, v_numIndParams_1449_, v_positions_1450_, v_k_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1458_, lean_object* v_inst_1459_, lean_object* v_below_1460_, lean_object* v_numIndParams_1461_, lean_object* v_positions_1462_, lean_object* v_k_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1458_, v_inst_1459_, v_below_1460_, v_numIndParams_1461_, v_positions_1462_, v_k_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_inst_1459_);
return v_res_1469_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = lean_unsigned_to_nat(32u);
v___x_1471_ = lean_mk_empty_array_with_capacity(v___x_1470_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1473_ = ((size_t)5ULL);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_unsigned_to_nat(32u);
v___x_1476_ = lean_mk_empty_array_with_capacity(v___x_1475_);
v___x_1477_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1478_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1476_);
lean_ctor_set(v___x_1478_, 2, v___x_1474_);
lean_ctor_set(v___x_1478_, 3, v___x_1474_);
lean_ctor_set_usize(v___x_1478_, 4, v___x_1473_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; lean_object* v_traceState_1482_; lean_object* v_traces_1483_; lean_object* v___x_1484_; lean_object* v_traceState_1485_; lean_object* v_env_1486_; lean_object* v_nextMacroScope_1487_; lean_object* v_ngen_1488_; lean_object* v_auxDeclNGen_1489_; lean_object* v_cache_1490_; lean_object* v_messages_1491_; lean_object* v_infoState_1492_; lean_object* v_snapshotTasks_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1512_; 
v___x_1481_ = lean_st_ref_get(v___y_1479_);
v_traceState_1482_ = lean_ctor_get(v___x_1481_, 4);
lean_inc_ref(v_traceState_1482_);
lean_dec(v___x_1481_);
v_traces_1483_ = lean_ctor_get(v_traceState_1482_, 0);
lean_inc_ref(v_traces_1483_);
lean_dec_ref(v_traceState_1482_);
v___x_1484_ = lean_st_ref_take(v___y_1479_);
v_traceState_1485_ = lean_ctor_get(v___x_1484_, 4);
v_env_1486_ = lean_ctor_get(v___x_1484_, 0);
v_nextMacroScope_1487_ = lean_ctor_get(v___x_1484_, 1);
v_ngen_1488_ = lean_ctor_get(v___x_1484_, 2);
v_auxDeclNGen_1489_ = lean_ctor_get(v___x_1484_, 3);
v_cache_1490_ = lean_ctor_get(v___x_1484_, 5);
v_messages_1491_ = lean_ctor_get(v___x_1484_, 6);
v_infoState_1492_ = lean_ctor_get(v___x_1484_, 7);
v_snapshotTasks_1493_ = lean_ctor_get(v___x_1484_, 8);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1495_ = v___x_1484_;
v_isShared_1496_ = v_isSharedCheck_1512_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snapshotTasks_1493_);
lean_inc(v_infoState_1492_);
lean_inc(v_messages_1491_);
lean_inc(v_cache_1490_);
lean_inc(v_traceState_1485_);
lean_inc(v_auxDeclNGen_1489_);
lean_inc(v_ngen_1488_);
lean_inc(v_nextMacroScope_1487_);
lean_inc(v_env_1486_);
lean_dec(v___x_1484_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1512_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
uint64_t v_tid_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1510_; 
v_tid_1497_ = lean_ctor_get_uint64(v_traceState_1485_, sizeof(void*)*1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_traceState_1485_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_traceState_1485_, 0);
lean_dec(v_unused_1511_);
v___x_1499_ = v_traceState_1485_;
v_isShared_1500_ = v_isSharedCheck_1510_;
goto v_resetjp_1498_;
}
else
{
lean_dec(v_traceState_1485_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1510_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1501_);
lean_ctor_set_uint64(v_reuseFailAlloc_1509_, sizeof(void*)*1, v_tid_1497_);
v___x_1503_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 4, v___x_1503_);
v___x_1505_ = v___x_1495_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_env_1486_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_nextMacroScope_1487_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_ngen_1488_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_auxDeclNGen_1489_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_cache_1490_);
lean_ctor_set(v_reuseFailAlloc_1508_, 6, v_messages_1491_);
lean_ctor_set(v_reuseFailAlloc_1508_, 7, v_infoState_1492_);
lean_ctor_set(v_reuseFailAlloc_1508_, 8, v_snapshotTasks_1493_);
v___x_1505_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_st_ref_put(v___y_1479_, v___x_1505_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_traces_1483_);
return v___x_1507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1513_);
lean_dec(v___y_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1527_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1528_, lean_object* v_opt_1529_){
_start:
{
lean_object* v_name_1530_; lean_object* v_defValue_1531_; lean_object* v_map_1532_; lean_object* v___x_1533_; 
v_name_1530_ = lean_ctor_get(v_opt_1529_, 0);
v_defValue_1531_ = lean_ctor_get(v_opt_1529_, 1);
v_map_1532_ = lean_ctor_get(v_opts_1528_, 0);
v___x_1533_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1532_, v_name_1530_);
if (lean_obj_tag(v___x_1533_) == 0)
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_unbox(v_defValue_1531_);
return v___x_1534_;
}
else
{
lean_object* v_val_1535_; 
v_val_1535_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v___x_1533_, 1);
if (lean_obj_tag(v_val_1535_) == 1)
{
uint8_t v_v_1536_; 
v_v_1536_ = lean_ctor_get_uint8(v_val_1535_, 0);
lean_dec_ref_known(v_val_1535_, 0);
return v_v_1536_;
}
else
{
uint8_t v___x_1537_; 
lean_dec(v_val_1535_);
v___x_1537_ = lean_unbox(v_defValue_1531_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1538_, lean_object* v_opt_1539_){
_start:
{
uint8_t v_res_1540_; lean_object* v_r_1541_; 
v_res_1540_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1538_, v_opt_1539_);
lean_dec_ref(v_opt_1539_);
lean_dec_ref(v_opts_1538_);
v_r_1541_ = lean_box(v_res_1540_);
return v_r_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1542_, lean_object* v_fnIndex_1543_, lean_object* v_recArg_1544_, lean_object* v_below_1545_, lean_object* v_Cs_1546_, lean_object* v_belowDict_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_array_get_borrowed(v___x_1542_, v_Cs_1546_, v_fnIndex_1543_);
lean_inc(v___x_1553_);
v___x_1554_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1553_, v_belowDict_1547_, v_recArg_1544_, v_below_1545_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1555_, lean_object* v_fnIndex_1556_, lean_object* v_recArg_1557_, lean_object* v_below_1558_, lean_object* v_Cs_1559_, lean_object* v_belowDict_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1555_, v_fnIndex_1556_, v_recArg_1557_, v_below_1558_, v_Cs_1559_, v_belowDict_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v_Cs_1559_);
lean_dec(v_fnIndex_1556_);
lean_dec_ref(v___x_1555_);
return v_res_1566_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1573_, lean_object* v_recArg_1574_, lean_object* v_x_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
v___x_1581_ = lean_infer_type(v_below_1573_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1596_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1596_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1596_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1586_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1587_ = l_Lean_MessageData_ofExpr(v_recArg_1574_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = l_Lean_MessageData_ofExpr(v_a_1582_);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1592_);
v___x_1594_ = v___x_1584_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v_recArg_1574_);
v_a_1597_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1581_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1581_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1605_, lean_object* v_recArg_1606_, lean_object* v_x_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1605_, v_recArg_1606_, v_x_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v_x_1607_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t v_sz_1614_, size_t v_i_1615_, lean_object* v_bs_1616_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_usize_dec_lt(v_i_1615_, v_sz_1614_);
if (v___x_1617_ == 0)
{
return v_bs_1616_;
}
else
{
lean_object* v_v_1618_; lean_object* v_msg_1619_; lean_object* v___x_1620_; lean_object* v_bs_x27_1621_; size_t v___x_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
v_v_1618_ = lean_array_uget_borrowed(v_bs_1616_, v_i_1615_);
v_msg_1619_ = lean_ctor_get(v_v_1618_, 1);
lean_inc_ref(v_msg_1619_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v_bs_x27_1621_ = lean_array_uset(v_bs_1616_, v_i_1615_, v___x_1620_);
v___x_1622_ = ((size_t)1ULL);
v___x_1623_ = lean_usize_add(v_i_1615_, v___x_1622_);
v___x_1624_ = lean_array_uset(v_bs_x27_1621_, v_i_1615_, v_msg_1619_);
v_i_1615_ = v___x_1623_;
v_bs_1616_ = v___x_1624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1626_, lean_object* v_i_1627_, lean_object* v_bs_1628_){
_start:
{
size_t v_sz_boxed_1629_; size_t v_i_boxed_1630_; lean_object* v_res_1631_; 
v_sz_boxed_1629_ = lean_unbox_usize(v_sz_1626_);
lean_dec(v_sz_1626_);
v_i_boxed_1630_ = lean_unbox_usize(v_i_1627_);
lean_dec(v_i_1627_);
v_res_1631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_boxed_1629_, v_i_boxed_1630_, v_bs_1628_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_oldTraces_1632_, lean_object* v_data_1633_, lean_object* v_ref_1634_, lean_object* v_msg_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_fileName_1641_; lean_object* v_fileMap_1642_; lean_object* v_options_1643_; lean_object* v_currRecDepth_1644_; lean_object* v_maxRecDepth_1645_; lean_object* v_ref_1646_; lean_object* v_currNamespace_1647_; lean_object* v_openDecls_1648_; lean_object* v_initHeartbeats_1649_; lean_object* v_maxHeartbeats_1650_; lean_object* v_quotContext_1651_; lean_object* v_currMacroScope_1652_; uint8_t v_diag_1653_; lean_object* v_cancelTk_x3f_1654_; uint8_t v_suppressElabErrors_1655_; lean_object* v_inheritedTraceOptions_1656_; lean_object* v___x_1657_; lean_object* v_traceState_1658_; lean_object* v_traces_1659_; lean_object* v_ref_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; size_t v_sz_1663_; size_t v___x_1664_; lean_object* v___x_1665_; lean_object* v_msg_1666_; lean_object* v___x_1667_; lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1705_; 
v_fileName_1641_ = lean_ctor_get(v___y_1638_, 0);
v_fileMap_1642_ = lean_ctor_get(v___y_1638_, 1);
v_options_1643_ = lean_ctor_get(v___y_1638_, 2);
v_currRecDepth_1644_ = lean_ctor_get(v___y_1638_, 3);
v_maxRecDepth_1645_ = lean_ctor_get(v___y_1638_, 4);
v_ref_1646_ = lean_ctor_get(v___y_1638_, 5);
v_currNamespace_1647_ = lean_ctor_get(v___y_1638_, 6);
v_openDecls_1648_ = lean_ctor_get(v___y_1638_, 7);
v_initHeartbeats_1649_ = lean_ctor_get(v___y_1638_, 8);
v_maxHeartbeats_1650_ = lean_ctor_get(v___y_1638_, 9);
v_quotContext_1651_ = lean_ctor_get(v___y_1638_, 10);
v_currMacroScope_1652_ = lean_ctor_get(v___y_1638_, 11);
v_diag_1653_ = lean_ctor_get_uint8(v___y_1638_, sizeof(void*)*14);
v_cancelTk_x3f_1654_ = lean_ctor_get(v___y_1638_, 12);
v_suppressElabErrors_1655_ = lean_ctor_get_uint8(v___y_1638_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1656_ = lean_ctor_get(v___y_1638_, 13);
v___x_1657_ = lean_st_ref_get(v___y_1639_);
v_traceState_1658_ = lean_ctor_get(v___x_1657_, 4);
lean_inc_ref(v_traceState_1658_);
lean_dec(v___x_1657_);
v_traces_1659_ = lean_ctor_get(v_traceState_1658_, 0);
lean_inc_ref(v_traces_1659_);
lean_dec_ref(v_traceState_1658_);
v_ref_1660_ = l_Lean_replaceRef(v_ref_1634_, v_ref_1646_);
lean_inc_ref(v_inheritedTraceOptions_1656_);
lean_inc(v_cancelTk_x3f_1654_);
lean_inc(v_currMacroScope_1652_);
lean_inc(v_quotContext_1651_);
lean_inc(v_maxHeartbeats_1650_);
lean_inc(v_initHeartbeats_1649_);
lean_inc(v_openDecls_1648_);
lean_inc(v_currNamespace_1647_);
lean_inc(v_maxRecDepth_1645_);
lean_inc(v_currRecDepth_1644_);
lean_inc_ref(v_options_1643_);
lean_inc_ref(v_fileMap_1642_);
lean_inc_ref(v_fileName_1641_);
v___x_1661_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1661_, 0, v_fileName_1641_);
lean_ctor_set(v___x_1661_, 1, v_fileMap_1642_);
lean_ctor_set(v___x_1661_, 2, v_options_1643_);
lean_ctor_set(v___x_1661_, 3, v_currRecDepth_1644_);
lean_ctor_set(v___x_1661_, 4, v_maxRecDepth_1645_);
lean_ctor_set(v___x_1661_, 5, v_ref_1660_);
lean_ctor_set(v___x_1661_, 6, v_currNamespace_1647_);
lean_ctor_set(v___x_1661_, 7, v_openDecls_1648_);
lean_ctor_set(v___x_1661_, 8, v_initHeartbeats_1649_);
lean_ctor_set(v___x_1661_, 9, v_maxHeartbeats_1650_);
lean_ctor_set(v___x_1661_, 10, v_quotContext_1651_);
lean_ctor_set(v___x_1661_, 11, v_currMacroScope_1652_);
lean_ctor_set(v___x_1661_, 12, v_cancelTk_x3f_1654_);
lean_ctor_set(v___x_1661_, 13, v_inheritedTraceOptions_1656_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*14, v_diag_1653_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*14 + 1, v_suppressElabErrors_1655_);
v___x_1662_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1659_);
lean_dec_ref(v_traces_1659_);
v_sz_1663_ = lean_array_size(v___x_1662_);
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1663_, v___x_1664_, v___x_1662_);
v_msg_1666_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1666_, 0, v_data_1633_);
lean_ctor_set(v_msg_1666_, 1, v_msg_1635_);
lean_ctor_set(v_msg_1666_, 2, v___x_1665_);
v___x_1667_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1666_, v___y_1636_, v___y_1637_, v___x_1661_, v___y_1639_);
lean_dec_ref_known(v___x_1661_, 14);
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1705_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1705_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v_traceState_1673_; lean_object* v_env_1674_; lean_object* v_nextMacroScope_1675_; lean_object* v_ngen_1676_; lean_object* v_auxDeclNGen_1677_; lean_object* v_cache_1678_; lean_object* v_messages_1679_; lean_object* v_infoState_1680_; lean_object* v_snapshotTasks_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1704_; 
v___x_1672_ = lean_st_ref_take(v___y_1639_);
v_traceState_1673_ = lean_ctor_get(v___x_1672_, 4);
v_env_1674_ = lean_ctor_get(v___x_1672_, 0);
v_nextMacroScope_1675_ = lean_ctor_get(v___x_1672_, 1);
v_ngen_1676_ = lean_ctor_get(v___x_1672_, 2);
v_auxDeclNGen_1677_ = lean_ctor_get(v___x_1672_, 3);
v_cache_1678_ = lean_ctor_get(v___x_1672_, 5);
v_messages_1679_ = lean_ctor_get(v___x_1672_, 6);
v_infoState_1680_ = lean_ctor_get(v___x_1672_, 7);
v_snapshotTasks_1681_ = lean_ctor_get(v___x_1672_, 8);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1683_ = v___x_1672_;
v_isShared_1684_ = v_isSharedCheck_1704_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_snapshotTasks_1681_);
lean_inc(v_infoState_1680_);
lean_inc(v_messages_1679_);
lean_inc(v_cache_1678_);
lean_inc(v_traceState_1673_);
lean_inc(v_auxDeclNGen_1677_);
lean_inc(v_ngen_1676_);
lean_inc(v_nextMacroScope_1675_);
lean_inc(v_env_1674_);
lean_dec(v___x_1672_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1704_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
uint64_t v_tid_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1702_; 
v_tid_1685_ = lean_ctor_get_uint64(v_traceState_1673_, sizeof(void*)*1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_traceState_1673_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v_traceState_1673_, 0);
lean_dec(v_unused_1703_);
v___x_1687_ = v_traceState_1673_;
v_isShared_1688_ = v_isSharedCheck_1702_;
goto v_resetjp_1686_;
}
else
{
lean_dec(v_traceState_1673_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1702_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_ref_1634_);
lean_ctor_set(v___x_1689_, 1, v_a_1668_);
v___x_1690_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1632_, v___x_1689_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1690_);
v___x_1692_ = v___x_1687_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1690_);
lean_ctor_set_uint64(v_reuseFailAlloc_1701_, sizeof(void*)*1, v_tid_1685_);
v___x_1692_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1694_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 4, v___x_1692_);
v___x_1694_ = v___x_1683_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_env_1674_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_nextMacroScope_1675_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_ngen_1676_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_auxDeclNGen_1677_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1700_, 5, v_cache_1678_);
lean_ctor_set(v_reuseFailAlloc_1700_, 6, v_messages_1679_);
lean_ctor_set(v_reuseFailAlloc_1700_, 7, v_infoState_1680_);
lean_ctor_set(v_reuseFailAlloc_1700_, 8, v_snapshotTasks_1681_);
v___x_1694_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1695_ = lean_st_ref_put(v___y_1639_, v___x_1694_);
v___x_1696_ = lean_box(0);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1696_);
v___x_1698_ = v___x_1670_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1706_, lean_object* v_data_1707_, lean_object* v_ref_1708_, lean_object* v_msg_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1706_, v_data_1707_, v_ref_1708_, v_msg_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1716_){
_start:
{
if (lean_obj_tag(v_e_1716_) == 0)
{
uint8_t v___x_1717_; 
v___x_1717_ = 2;
return v___x_1717_;
}
else
{
lean_object* v_a_1718_; uint8_t v___x_1719_; 
v_a_1718_ = lean_ctor_get(v_e_1716_, 0);
v___x_1719_ = l_Lean_Expr_hasSyntheticSorry(v_a_1718_);
if (v___x_1719_ == 0)
{
uint8_t v___x_1720_; 
v___x_1720_ = 0;
return v___x_1720_;
}
else
{
uint8_t v___x_1721_; 
v___x_1721_ = 1;
return v___x_1721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1722_){
_start:
{
uint8_t v_res_1723_; lean_object* v_r_1724_; 
v_res_1723_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1722_);
lean_dec_ref(v_e_1722_);
v_r_1724_ = lean_box(v_res_1723_);
return v_r_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1725_, lean_object* v_opt_1726_){
_start:
{
lean_object* v_name_1727_; lean_object* v_defValue_1728_; lean_object* v_map_1729_; lean_object* v___x_1730_; 
v_name_1727_ = lean_ctor_get(v_opt_1726_, 0);
v_defValue_1728_ = lean_ctor_get(v_opt_1726_, 1);
v_map_1729_ = lean_ctor_get(v_opts_1725_, 0);
v___x_1730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1729_, v_name_1727_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_inc(v_defValue_1728_);
return v_defValue_1728_;
}
else
{
lean_object* v_val_1731_; 
v_val_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v___x_1730_, 1);
if (lean_obj_tag(v_val_1731_) == 3)
{
lean_object* v_v_1732_; 
v_v_1732_ = lean_ctor_get(v_val_1731_, 0);
lean_inc(v_v_1732_);
lean_dec_ref_known(v_val_1731_, 1);
return v_v_1732_;
}
else
{
lean_dec(v_val_1731_);
lean_inc(v_defValue_1728_);
return v_defValue_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1733_, lean_object* v_opt_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1733_, v_opt_1734_);
lean_dec_ref(v_opt_1734_);
lean_dec_ref(v_opts_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
v_a_1738_ = lean_ctor_get(v_x_1736_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_x_1736_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v_x_1736_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v_x_1736_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 1);
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
v_a_1746_ = lean_ctor_get(v_x_1736_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x_1736_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v_x_1736_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v_x_1736_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 0);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1754_);
return v_res_1756_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1759_ = l_Lean_stringToMessageData(v___x_1758_);
return v___x_1759_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1760_; double v___x_1761_; 
v___x_1760_ = lean_unsigned_to_nat(1000u);
v___x_1761_ = lean_float_of_nat(v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1762_, uint8_t v_collapsed_1763_, lean_object* v_tag_1764_, lean_object* v_opts_1765_, uint8_t v_clsEnabled_1766_, lean_object* v_oldTraces_1767_, lean_object* v_msg_1768_, lean_object* v_resStartStop_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_fst_1775_; lean_object* v_snd_1776_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v_data_1780_; lean_object* v_fst_1791_; lean_object* v_snd_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___y_1796_; lean_object* v_a_1797_; uint8_t v___y_1812_; double v___y_1843_; 
v_fst_1775_ = lean_ctor_get(v_resStartStop_1769_, 0);
lean_inc(v_fst_1775_);
v_snd_1776_ = lean_ctor_get(v_resStartStop_1769_, 1);
lean_inc(v_snd_1776_);
lean_dec_ref(v_resStartStop_1769_);
v_fst_1791_ = lean_ctor_get(v_snd_1776_, 0);
lean_inc(v_fst_1791_);
v_snd_1792_ = lean_ctor_get(v_snd_1776_, 1);
lean_inc(v_snd_1792_);
lean_dec(v_snd_1776_);
v___x_1793_ = l_Lean_trace_profiler;
v___x_1794_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1765_, v___x_1793_);
if (v___x_1794_ == 0)
{
v___y_1812_ = v___x_1794_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1849_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1765_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; double v___x_1852_; double v___x_1853_; double v___x_1854_; 
v___x_1850_ = l_Lean_trace_profiler_threshold;
v___x_1851_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1765_, v___x_1850_);
v___x_1852_ = lean_float_of_nat(v___x_1851_);
v___x_1853_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2);
v___x_1854_ = lean_float_div(v___x_1852_, v___x_1853_);
v___y_1843_ = v___x_1854_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; double v___x_1857_; 
v___x_1855_ = l_Lean_trace_profiler_threshold;
v___x_1856_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1765_, v___x_1855_);
v___x_1857_ = lean_float_of_nat(v___x_1856_);
v___y_1843_ = v___x_1857_;
goto v___jp_1842_;
}
}
v___jp_1777_:
{
lean_object* v___x_1781_; 
lean_inc(v___y_1779_);
v___x_1781_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1767_, v_data_1780_, v___y_1779_, v___y_1778_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v___x_1782_; 
lean_dec_ref_known(v___x_1781_, 1);
v___x_1782_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1775_);
return v___x_1782_;
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_fst_1775_);
v_a_1783_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1781_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
v___jp_1795_:
{
uint8_t v_result_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; double v___x_1801_; lean_object* v_data_1802_; 
v_result_1798_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1775_);
v___x_1799_ = lean_box(v_result_1798_);
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
v___x_1801_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1764_);
lean_inc_ref(v___x_1800_);
lean_inc(v_cls_1762_);
v_data_1802_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1802_, 0, v_cls_1762_);
lean_ctor_set(v_data_1802_, 1, v___x_1800_);
lean_ctor_set(v_data_1802_, 2, v_tag_1764_);
lean_ctor_set_float(v_data_1802_, sizeof(void*)*3, v___x_1801_);
lean_ctor_set_float(v_data_1802_, sizeof(void*)*3 + 8, v___x_1801_);
lean_ctor_set_uint8(v_data_1802_, sizeof(void*)*3 + 16, v_collapsed_1763_);
if (v___x_1794_ == 0)
{
lean_dec_ref_known(v___x_1800_, 1);
lean_dec(v_snd_1792_);
lean_dec(v_fst_1791_);
lean_dec_ref(v_tag_1764_);
lean_dec(v_cls_1762_);
v___y_1778_ = v_a_1797_;
v___y_1779_ = v___y_1796_;
v_data_1780_ = v_data_1802_;
goto v___jp_1777_;
}
else
{
lean_object* v_data_1803_; double v___x_1804_; double v___x_1805_; 
lean_dec_ref_known(v_data_1802_, 3);
v_data_1803_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1803_, 0, v_cls_1762_);
lean_ctor_set(v_data_1803_, 1, v___x_1800_);
lean_ctor_set(v_data_1803_, 2, v_tag_1764_);
v___x_1804_ = lean_unbox_float(v_fst_1791_);
lean_dec(v_fst_1791_);
lean_ctor_set_float(v_data_1803_, sizeof(void*)*3, v___x_1804_);
v___x_1805_ = lean_unbox_float(v_snd_1792_);
lean_dec(v_snd_1792_);
lean_ctor_set_float(v_data_1803_, sizeof(void*)*3 + 8, v___x_1805_);
lean_ctor_set_uint8(v_data_1803_, sizeof(void*)*3 + 16, v_collapsed_1763_);
v___y_1778_ = v_a_1797_;
v___y_1779_ = v___y_1796_;
v_data_1780_ = v_data_1803_;
goto v___jp_1777_;
}
}
v___jp_1806_:
{
lean_object* v_ref_1807_; lean_object* v___x_1808_; 
v_ref_1807_ = lean_ctor_get(v___y_1772_, 5);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
lean_inc(v___y_1771_);
lean_inc_ref(v___y_1770_);
lean_inc(v_fst_1775_);
v___x_1808_ = lean_apply_6(v_msg_1768_, v_fst_1775_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, lean_box(0));
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___y_1796_ = v_ref_1807_;
v_a_1797_ = v_a_1809_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1810_; 
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
v___y_1796_ = v_ref_1807_;
v_a_1797_ = v___x_1810_;
goto v___jp_1795_;
}
}
v___jp_1811_:
{
if (v_clsEnabled_1766_ == 0)
{
if (v___y_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v_traceState_1814_; lean_object* v_env_1815_; lean_object* v_nextMacroScope_1816_; lean_object* v_ngen_1817_; lean_object* v_auxDeclNGen_1818_; lean_object* v_cache_1819_; lean_object* v_messages_1820_; lean_object* v_infoState_1821_; lean_object* v_snapshotTasks_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v_snd_1792_);
lean_dec(v_fst_1791_);
lean_dec_ref(v_msg_1768_);
lean_dec_ref(v_tag_1764_);
lean_dec(v_cls_1762_);
v___x_1813_ = lean_st_ref_take(v___y_1773_);
v_traceState_1814_ = lean_ctor_get(v___x_1813_, 4);
v_env_1815_ = lean_ctor_get(v___x_1813_, 0);
v_nextMacroScope_1816_ = lean_ctor_get(v___x_1813_, 1);
v_ngen_1817_ = lean_ctor_get(v___x_1813_, 2);
v_auxDeclNGen_1818_ = lean_ctor_get(v___x_1813_, 3);
v_cache_1819_ = lean_ctor_get(v___x_1813_, 5);
v_messages_1820_ = lean_ctor_get(v___x_1813_, 6);
v_infoState_1821_ = lean_ctor_get(v___x_1813_, 7);
v_snapshotTasks_1822_ = lean_ctor_get(v___x_1813_, 8);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1824_ = v___x_1813_;
v_isShared_1825_ = v_isSharedCheck_1841_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_snapshotTasks_1822_);
lean_inc(v_infoState_1821_);
lean_inc(v_messages_1820_);
lean_inc(v_cache_1819_);
lean_inc(v_traceState_1814_);
lean_inc(v_auxDeclNGen_1818_);
lean_inc(v_ngen_1817_);
lean_inc(v_nextMacroScope_1816_);
lean_inc(v_env_1815_);
lean_dec(v___x_1813_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1841_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
uint64_t v_tid_1826_; lean_object* v_traces_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1840_; 
v_tid_1826_ = lean_ctor_get_uint64(v_traceState_1814_, sizeof(void*)*1);
v_traces_1827_ = lean_ctor_get(v_traceState_1814_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_traceState_1814_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1829_ = v_traceState_1814_;
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_traces_1827_);
lean_dec(v_traceState_1814_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1767_, v_traces_1827_);
lean_dec_ref(v_traces_1827_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1831_);
lean_ctor_set_uint64(v_reuseFailAlloc_1839_, sizeof(void*)*1, v_tid_1826_);
v___x_1833_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 4, v___x_1833_);
v___x_1835_ = v___x_1824_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_env_1815_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_nextMacroScope_1816_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_ngen_1817_);
lean_ctor_set(v_reuseFailAlloc_1838_, 3, v_auxDeclNGen_1818_);
lean_ctor_set(v_reuseFailAlloc_1838_, 4, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1838_, 5, v_cache_1819_);
lean_ctor_set(v_reuseFailAlloc_1838_, 6, v_messages_1820_);
lean_ctor_set(v_reuseFailAlloc_1838_, 7, v_infoState_1821_);
lean_ctor_set(v_reuseFailAlloc_1838_, 8, v_snapshotTasks_1822_);
v___x_1835_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_st_ref_put(v___y_1773_, v___x_1835_);
v___x_1837_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1775_);
return v___x_1837_;
}
}
}
}
}
else
{
goto v___jp_1806_;
}
}
else
{
goto v___jp_1806_;
}
}
v___jp_1842_:
{
double v___x_1844_; double v___x_1845_; double v___x_1846_; uint8_t v___x_1847_; 
v___x_1844_ = lean_unbox_float(v_snd_1792_);
v___x_1845_ = lean_unbox_float(v_fst_1791_);
v___x_1846_ = lean_float_sub(v___x_1844_, v___x_1845_);
v___x_1847_ = lean_float_decLt(v___y_1843_, v___x_1846_);
v___y_1812_ = v___x_1847_;
goto v___jp_1811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1858_, lean_object* v_collapsed_1859_, lean_object* v_tag_1860_, lean_object* v_opts_1861_, lean_object* v_clsEnabled_1862_, lean_object* v_oldTraces_1863_, lean_object* v_msg_1864_, lean_object* v_resStartStop_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
uint8_t v_collapsed_boxed_1871_; uint8_t v_clsEnabled_boxed_1872_; lean_object* v_res_1873_; 
v_collapsed_boxed_1871_ = lean_unbox(v_collapsed_1859_);
v_clsEnabled_boxed_1872_ = lean_unbox(v_clsEnabled_1862_);
v_res_1873_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1858_, v_collapsed_boxed_1871_, v_tag_1860_, v_opts_1861_, v_clsEnabled_boxed_1872_, v_oldTraces_1863_, v_msg_1864_, v_resStartStop_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v_opts_1861_);
return v_res_1873_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1875_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1876_ = l_Lean_Name_append(v___x_1875_, v___x_1874_);
return v___x_1876_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__1(void){
_start:
{
lean_object* v___x_1877_; double v___x_1878_; 
v___x_1877_ = lean_unsigned_to_nat(1000000000u);
v___x_1878_ = lean_float_of_nat(v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1879_, lean_object* v_numIndParams_1880_, lean_object* v_positions_1881_, lean_object* v_fnIndex_1882_, lean_object* v_recArg_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_options_1889_; lean_object* v_inheritedTraceOptions_1890_; uint8_t v_hasTrace_1891_; lean_object* v___x_1892_; lean_object* v___f_1893_; 
v_options_1889_ = lean_ctor_get(v_a_1886_, 2);
v_inheritedTraceOptions_1890_ = lean_ctor_get(v_a_1886_, 13);
v_hasTrace_1891_ = lean_ctor_get_uint8(v_options_1889_, sizeof(void*)*1);
v___x_1892_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1879_);
lean_inc_ref(v_recArg_1883_);
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1893_, 0, v___x_1892_);
lean_closure_set(v___f_1893_, 1, v_fnIndex_1882_);
lean_closure_set(v___f_1893_, 2, v_recArg_1883_);
lean_closure_set(v___f_1893_, 3, v_below_1879_);
if (v_hasTrace_1891_ == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref(v_recArg_1883_);
v___x_1894_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1879_, v_numIndParams_1880_, v_positions_1881_, v___f_1893_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1894_;
}
else
{
lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v_a_1903_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v_a_1918_; 
lean_inc_ref(v_below_1879_);
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1895_, 0, v_below_1879_);
lean_closure_set(v___f_1895_, 1, v_recArg_1883_);
v___x_1896_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1897_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1898_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1899_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1890_, v_options_1889_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = l_Lean_trace_profiler;
v___x_1969_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1889_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref(v___f_1895_);
v___x_1970_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1879_, v_numIndParams_1880_, v_positions_1881_, v___f_1893_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1970_;
}
else
{
goto v___jp_1927_;
}
}
else
{
goto v___jp_1927_;
}
v___jp_1900_:
{
lean_object* v___x_1904_; double v___x_1905_; double v___x_1906_; double v___x_1907_; double v___x_1908_; double v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1904_ = lean_io_mono_nanos_now();
v___x_1905_ = lean_float_of_nat(v___y_1901_);
v___x_1906_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__1, &l_Lean_Elab_Structural_toBelow___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___closed__1);
v___x_1907_ = lean_float_div(v___x_1905_, v___x_1906_);
v___x_1908_ = lean_float_of_nat(v___x_1904_);
v___x_1909_ = lean_float_div(v___x_1908_, v___x_1906_);
v___x_1910_ = lean_box_float(v___x_1907_);
v___x_1911_ = lean_box_float(v___x_1909_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_a_1903_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1896_, v_hasTrace_1891_, v___x_1897_, v_options_1889_, v___x_1899_, v___y_1902_, v___f_1895_, v___x_1913_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1914_;
}
v___jp_1915_:
{
lean_object* v___x_1919_; double v___x_1920_; double v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1919_ = lean_io_get_num_heartbeats();
v___x_1920_ = lean_float_of_nat(v___y_1917_);
v___x_1921_ = lean_float_of_nat(v___x_1919_);
v___x_1922_ = lean_box_float(v___x_1920_);
v___x_1923_ = lean_box_float(v___x_1921_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1918_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1896_, v_hasTrace_1891_, v___x_1897_, v_options_1889_, v___x_1899_, v___y_1916_, v___f_1895_, v___x_1925_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1926_;
}
v___jp_1927_:
{
lean_object* v___x_1928_; lean_object* v_a_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1928_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1887_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1931_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1889_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_io_mono_nanos_now();
v___x_1933_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1879_, v_numIndParams_1880_, v_positions_1881_, v___f_1893_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 1);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
v___y_1901_ = v___x_1932_;
v___y_1902_ = v_a_1929_;
v_a_1903_ = v___x_1939_;
goto v___jp_1900_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 0);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v___y_1901_ = v___x_1932_;
v___y_1902_ = v_a_1929_;
v_a_1903_ = v___x_1947_;
goto v___jp_1900_;
}
}
}
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = lean_io_get_num_heartbeats();
v___x_1951_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1879_, v_numIndParams_1880_, v_positions_1881_, v___f_1893_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 1);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
v___y_1916_ = v_a_1929_;
v___y_1917_ = v___x_1950_;
v_a_1918_ = v___x_1957_;
goto v___jp_1915_;
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
v_a_1960_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1951_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1951_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set_tag(v___x_1962_, 0);
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
v___y_1916_ = v_a_1929_;
v___y_1917_ = v___x_1950_;
v_a_1918_ = v___x_1965_;
goto v___jp_1915_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1971_, lean_object* v_numIndParams_1972_, lean_object* v_positions_1973_, lean_object* v_fnIndex_1974_, lean_object* v_recArg_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Elab_Structural_toBelow(v_below_1971_, v_numIndParams_1972_, v_positions_1973_, v_fnIndex_1974_, v_recArg_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1983_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_x_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1990_, v_x_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1998_, lean_object* v___y_1999_, lean_object* v_b_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___x_2006_; 
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
lean_inc(v___y_1999_);
v___x_2006_ = lean_apply_7(v_k_1998_, v_b_2000_, v___y_1999_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, lean_box(0));
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_2007_, lean_object* v___y_2008_, lean_object* v_b_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_2007_, v___y_2008_, v_b_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2008_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_2016_, uint8_t v_bi_2017_, lean_object* v_type_2018_, lean_object* v_k_2019_, uint8_t v_kind_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___f_2027_; lean_object* v___x_2028_; 
lean_inc(v___y_2021_);
v___f_2027_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2027_, 0, v_k_2019_);
lean_closure_set(v___f_2027_, 1, v___y_2021_);
v___x_2028_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2016_, v_bi_2017_, v_type_2018_, v___f_2027_, v_kind_2020_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2028_) == 0)
{
return v___x_2028_;
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_2037_, lean_object* v_bi_2038_, lean_object* v_type_2039_, lean_object* v_k_2040_, lean_object* v_kind_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_bi_boxed_2048_; uint8_t v_kind_boxed_2049_; lean_object* v_res_2050_; 
v_bi_boxed_2048_ = lean_unbox(v_bi_2038_);
v_kind_boxed_2049_ = lean_unbox(v_kind_2041_);
v_res_2050_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2037_, v_bi_boxed_2048_, v_type_2039_, v_k_2040_, v_kind_boxed_2049_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2051_, lean_object* v_name_2052_, uint8_t v_bi_2053_, lean_object* v_type_2054_, lean_object* v_k_2055_, uint8_t v_kind_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2052_, v_bi_2053_, v_type_2054_, v_k_2055_, v_kind_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2064_, lean_object* v_name_2065_, lean_object* v_bi_2066_, lean_object* v_type_2067_, lean_object* v_k_2068_, lean_object* v_kind_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v_bi_boxed_2076_; uint8_t v_kind_boxed_2077_; lean_object* v_res_2078_; 
v_bi_boxed_2076_ = lean_unbox(v_bi_2066_);
v_kind_boxed_2077_ = lean_unbox(v_kind_2069_);
v_res_2078_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2064_, v_name_2065_, v_bi_boxed_2076_, v_type_2067_, v_k_2068_, v_kind_boxed_2077_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2079_, lean_object* v___y_2080_, lean_object* v_b_2081_, lean_object* v_c_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; 
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2080_);
v___x_2088_ = lean_apply_8(v_k_2079_, v_b_2081_, v_c_2082_, v___y_2080_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, lean_box(0));
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2089_, lean_object* v___y_2090_, lean_object* v_b_2091_, lean_object* v_c_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2089_, v___y_2090_, v_b_2091_, v_c_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2090_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2099_, lean_object* v_maxFVars_2100_, lean_object* v_k_2101_, uint8_t v_cleanupAnnotations_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___f_2109_; uint8_t v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_inc(v___y_2103_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2109_, 0, v_k_2101_);
lean_closure_set(v___f_2109_, 1, v___y_2103_);
v___x_2110_ = 1;
v___x_2111_ = 0;
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_maxFVars_2100_);
v___x_2113_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2099_, v___x_2110_, v___x_2111_, v___x_2110_, v___x_2111_, v___x_2112_, v___f_2109_, v_cleanupAnnotations_2102_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec_ref_known(v___x_2112_, 1);
if (lean_obj_tag(v___x_2113_) == 0)
{
return v___x_2113_;
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2122_, lean_object* v_maxFVars_2123_, lean_object* v_k_2124_, lean_object* v_cleanupAnnotations_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2132_; lean_object* v_res_2133_; 
v_cleanupAnnotations_boxed_2132_ = lean_unbox(v_cleanupAnnotations_2125_);
v_res_2133_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2122_, v_maxFVars_2123_, v_k_2124_, v_cleanupAnnotations_boxed_2132_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2134_, lean_object* v_e_2135_, lean_object* v_maxFVars_2136_, lean_object* v_k_2137_, uint8_t v_cleanupAnnotations_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2135_, v_maxFVars_2136_, v_k_2137_, v_cleanupAnnotations_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2146_, lean_object* v_e_2147_, lean_object* v_maxFVars_2148_, lean_object* v_k_2149_, lean_object* v_cleanupAnnotations_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2157_; lean_object* v_res_2158_; 
v_cleanupAnnotations_boxed_2157_ = lean_unbox(v_cleanupAnnotations_2150_);
v_res_2158_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2146_, v_e_2147_, v_maxFVars_2148_, v_k_2149_, v_cleanupAnnotations_boxed_2157_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2159_, lean_object* v_type_2160_, lean_object* v_val_2161_, lean_object* v_k_2162_, uint8_t v_nondep_2163_, uint8_t v_kind_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v___f_2171_; lean_object* v___x_2172_; 
lean_inc(v___y_2165_);
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2171_, 0, v_k_2162_);
lean_closure_set(v___f_2171_, 1, v___y_2165_);
v___x_2172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2159_, v_type_2160_, v_val_2161_, v___f_2171_, v_nondep_2163_, v_kind_2164_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2172_) == 0)
{
return v___x_2172_;
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2181_, lean_object* v_type_2182_, lean_object* v_val_2183_, lean_object* v_k_2184_, lean_object* v_nondep_2185_, lean_object* v_kind_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
uint8_t v_nondep_boxed_2193_; uint8_t v_kind_boxed_2194_; lean_object* v_res_2195_; 
v_nondep_boxed_2193_ = lean_unbox(v_nondep_2185_);
v_kind_boxed_2194_ = lean_unbox(v_kind_2186_);
v_res_2195_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2181_, v_type_2182_, v_val_2183_, v_k_2184_, v_nondep_boxed_2193_, v_kind_boxed_2194_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2196_, uint8_t v_usedLetOnly_2197_, lean_object* v_x_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
lean_inc(v___y_2203_);
lean_inc_ref(v___y_2202_);
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
lean_inc(v___y_2199_);
lean_inc_ref(v_x_2198_);
v___x_2205_ = lean_apply_7(v_k_2196_, v_x_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, lean_box(0));
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_mk_empty_array_with_capacity(v___x_2207_);
v___x_2209_ = lean_array_push(v___x_2208_, v_x_2198_);
v___x_2210_ = 0;
v___x_2211_ = 1;
v___x_2212_ = l_Lean_Meta_mkLetFVars(v___x_2209_, v_a_2206_, v_usedLetOnly_2197_, v___x_2210_, v___x_2211_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec_ref(v___x_2209_);
return v___x_2212_;
}
else
{
lean_dec_ref(v_x_2198_);
return v___x_2205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2213_, lean_object* v_usedLetOnly_2214_, lean_object* v_x_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v_usedLetOnly_boxed_2222_; lean_object* v_res_2223_; 
v_usedLetOnly_boxed_2222_ = lean_unbox(v_usedLetOnly_2214_);
v_res_2223_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2213_, v_usedLetOnly_boxed_2222_, v_x_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2224_, lean_object* v_type_2225_, lean_object* v_val_2226_, lean_object* v_k_2227_, uint8_t v_nondep_2228_, uint8_t v_kind_2229_, uint8_t v_usedLetOnly_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; 
v___x_2237_ = lean_box(v_usedLetOnly_2230_);
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2238_, 0, v_k_2227_);
lean_closure_set(v___f_2238_, 1, v___x_2237_);
v___x_2239_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2224_, v_type_2225_, v_val_2226_, v___f_2238_, v_nondep_2228_, v_kind_2229_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2240_, lean_object* v_type_2241_, lean_object* v_val_2242_, lean_object* v_k_2243_, lean_object* v_nondep_2244_, lean_object* v_kind_2245_, lean_object* v_usedLetOnly_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint8_t v_nondep_boxed_2253_; uint8_t v_kind_boxed_2254_; uint8_t v_usedLetOnly_boxed_2255_; lean_object* v_res_2256_; 
v_nondep_boxed_2253_ = lean_unbox(v_nondep_2244_);
v_kind_boxed_2254_ = lean_unbox(v_kind_2245_);
v_usedLetOnly_boxed_2255_ = lean_unbox(v_usedLetOnly_2246_);
v_res_2256_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2240_, v_type_2241_, v_val_2242_, v_k_2243_, v_nondep_boxed_2253_, v_kind_boxed_2254_, v_usedLetOnly_boxed_2255_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
return v_res_2256_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2257_, lean_object* v_as_2258_, size_t v_i_2259_, size_t v_stop_2260_){
_start:
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_usize_dec_eq(v_i_2259_, v_stop_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v_fnName_2263_; lean_object* v_recArgPos_2264_; uint8_t v___x_2265_; 
v___x_2262_ = lean_array_uget_borrowed(v_as_2258_, v_i_2259_);
v_fnName_2263_ = lean_ctor_get(v___x_2262_, 0);
v_recArgPos_2264_ = lean_ctor_get(v___x_2262_, 2);
lean_inc(v_recArgPos_2264_);
lean_inc(v_fnName_2263_);
v___x_2265_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2263_, v_recArgPos_2264_, v_e_2257_);
if (v___x_2265_ == 0)
{
size_t v___x_2266_; size_t v___x_2267_; 
v___x_2266_ = ((size_t)1ULL);
v___x_2267_ = lean_usize_add(v_i_2259_, v___x_2266_);
v_i_2259_ = v___x_2267_;
goto _start;
}
else
{
return v___x_2265_;
}
}
else
{
uint8_t v___x_2269_; 
v___x_2269_ = 0;
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2270_, lean_object* v_as_2271_, lean_object* v_i_2272_, lean_object* v_stop_2273_){
_start:
{
size_t v_i_boxed_2274_; size_t v_stop_boxed_2275_; uint8_t v_res_2276_; lean_object* v_r_2277_; 
v_i_boxed_2274_ = lean_unbox_usize(v_i_2272_);
lean_dec(v_i_2272_);
v_stop_boxed_2275_ = lean_unbox_usize(v_stop_2273_);
lean_dec(v_stop_2273_);
v_res_2276_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2270_, v_as_2271_, v_i_boxed_2274_, v_stop_boxed_2275_);
lean_dec_ref(v_as_2271_);
lean_dec_ref(v_e_2270_);
v_r_2277_ = lean_box(v_res_2276_);
return v_r_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2278_, lean_object* v_____do__lift_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_options_2286_; uint8_t v_hasTrace_2287_; 
v_options_2286_ = lean_ctor_get(v___y_2283_, 2);
v_hasTrace_2287_ = lean_ctor_get_uint8(v_options_2286_, sizeof(void*)*1);
if (v_hasTrace_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec(v___x_2278_);
v___x_2288_ = lean_box(v_hasTrace_2287_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2290_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2291_ = l_Lean_Name_append(v___x_2290_, v___x_2278_);
v___x_2292_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2279_, v_options_2286_, v___x_2291_);
lean_dec(v___x_2291_);
v___x_2293_ = lean_box(v___x_2292_);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2295_, lean_object* v_____do__lift_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2295_, v_____do__lift_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v_____do__lift_2296_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2304_, lean_object* v_msg_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_ref_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2357_; 
v_ref_2311_ = lean_ctor_get(v___y_2308_, 5);
v___x_2312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2357_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2357_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v_traceState_2318_; lean_object* v_env_2319_; lean_object* v_nextMacroScope_2320_; lean_object* v_ngen_2321_; lean_object* v_auxDeclNGen_2322_; lean_object* v_cache_2323_; lean_object* v_messages_2324_; lean_object* v_infoState_2325_; lean_object* v_snapshotTasks_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2356_; 
v___x_2317_ = lean_st_ref_take(v___y_2309_);
v_traceState_2318_ = lean_ctor_get(v___x_2317_, 4);
v_env_2319_ = lean_ctor_get(v___x_2317_, 0);
v_nextMacroScope_2320_ = lean_ctor_get(v___x_2317_, 1);
v_ngen_2321_ = lean_ctor_get(v___x_2317_, 2);
v_auxDeclNGen_2322_ = lean_ctor_get(v___x_2317_, 3);
v_cache_2323_ = lean_ctor_get(v___x_2317_, 5);
v_messages_2324_ = lean_ctor_get(v___x_2317_, 6);
v_infoState_2325_ = lean_ctor_get(v___x_2317_, 7);
v_snapshotTasks_2326_ = lean_ctor_get(v___x_2317_, 8);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2328_ = v___x_2317_;
v_isShared_2329_ = v_isSharedCheck_2356_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snapshotTasks_2326_);
lean_inc(v_infoState_2325_);
lean_inc(v_messages_2324_);
lean_inc(v_cache_2323_);
lean_inc(v_traceState_2318_);
lean_inc(v_auxDeclNGen_2322_);
lean_inc(v_ngen_2321_);
lean_inc(v_nextMacroScope_2320_);
lean_inc(v_env_2319_);
lean_dec(v___x_2317_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2356_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
uint64_t v_tid_2330_; lean_object* v_traces_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2355_; 
v_tid_2330_ = lean_ctor_get_uint64(v_traceState_2318_, sizeof(void*)*1);
v_traces_2331_ = lean_ctor_get(v_traceState_2318_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_traceState_2318_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2333_ = v_traceState_2318_;
v_isShared_2334_ = v_isSharedCheck_2355_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_traces_2331_);
lean_dec(v_traceState_2318_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2355_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; double v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2337_ = 0;
v___x_2338_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2339_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2339_, 0, v_cls_2304_);
lean_ctor_set(v___x_2339_, 1, v___x_2335_);
lean_ctor_set(v___x_2339_, 2, v___x_2338_);
lean_ctor_set_float(v___x_2339_, sizeof(void*)*3, v___x_2336_);
lean_ctor_set_float(v___x_2339_, sizeof(void*)*3 + 8, v___x_2336_);
lean_ctor_set_uint8(v___x_2339_, sizeof(void*)*3 + 16, v___x_2337_);
v___x_2340_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2341_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v_a_2313_);
lean_ctor_set(v___x_2341_, 2, v___x_2340_);
lean_inc(v_ref_2311_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v_ref_2311_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = l_Lean_PersistentArray_push___redArg(v_traces_2331_, v___x_2342_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2343_);
v___x_2345_ = v___x_2333_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2343_);
lean_ctor_set_uint64(v_reuseFailAlloc_2354_, sizeof(void*)*1, v_tid_2330_);
v___x_2345_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 4, v___x_2345_);
v___x_2347_ = v___x_2328_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_env_2319_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_nextMacroScope_2320_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_ngen_2321_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v_auxDeclNGen_2322_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2353_, 5, v_cache_2323_);
lean_ctor_set(v_reuseFailAlloc_2353_, 6, v_messages_2324_);
lean_ctor_set(v_reuseFailAlloc_2353_, 7, v_infoState_2325_);
lean_ctor_set(v_reuseFailAlloc_2353_, 8, v_snapshotTasks_2326_);
v___x_2347_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2348_ = lean_st_ref_put(v___y_2309_, v___x_2347_);
v___x_2349_ = lean_box(0);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2349_);
v___x_2351_ = v___x_2315_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2358_, lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2358_, v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; lean_object* v_env_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2369_ = lean_st_ref_get(v___y_2367_);
v_env_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc_ref(v_env_2370_);
lean_dec(v___x_2369_);
v___x_2371_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2370_, v_declName_2366_);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2373_, v___y_2374_);
lean_dec(v___y_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_2384_; lean_object* v_toApplicative_2385_; lean_object* v_toFunctor_2386_; lean_object* v_toSeq_2387_; lean_object* v_toSeqLeft_2388_; lean_object* v_toSeqRight_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___f_2395_; lean_object* v___f_2396_; lean_object* v___f_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v_toApplicative_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2433_; 
v___x_2384_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2385_ = lean_ctor_get(v___x_2384_, 0);
v_toFunctor_2386_ = lean_ctor_get(v_toApplicative_2385_, 0);
v_toSeq_2387_ = lean_ctor_get(v_toApplicative_2385_, 2);
v_toSeqLeft_2388_ = lean_ctor_get(v_toApplicative_2385_, 3);
v_toSeqRight_2389_ = lean_ctor_get(v_toApplicative_2385_, 4);
v___f_2390_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2391_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2386_, 2);
v___f_2392_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2392_, 0, v_toFunctor_2386_);
v___f_2393_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2393_, 0, v_toFunctor_2386_);
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___f_2392_);
lean_ctor_set(v___x_2394_, 1, v___f_2393_);
lean_inc(v_toSeqRight_2389_);
v___f_2395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2395_, 0, v_toSeqRight_2389_);
lean_inc(v_toSeqLeft_2388_);
v___f_2396_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2396_, 0, v_toSeqLeft_2388_);
lean_inc(v_toSeq_2387_);
v___f_2397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2397_, 0, v_toSeq_2387_);
v___x_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2394_);
lean_ctor_set(v___x_2398_, 1, v___f_2390_);
lean_ctor_set(v___x_2398_, 2, v___f_2397_);
lean_ctor_set(v___x_2398_, 3, v___f_2396_);
lean_ctor_set(v___x_2398_, 4, v___f_2395_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set(v___x_2399_, 1, v___f_2391_);
v___x_2400_ = l_StateRefT_x27_instMonad___redArg(v___x_2399_);
v_toApplicative_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; 
v_unused_2434_ = lean_ctor_get(v___x_2400_, 1);
lean_dec(v_unused_2434_);
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2433_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_toApplicative_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2433_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_toFunctor_2405_; lean_object* v_toSeq_2406_; lean_object* v_toSeqLeft_2407_; lean_object* v_toSeqRight_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2431_; 
v_toFunctor_2405_ = lean_ctor_get(v_toApplicative_2401_, 0);
v_toSeq_2406_ = lean_ctor_get(v_toApplicative_2401_, 2);
v_toSeqLeft_2407_ = lean_ctor_get(v_toApplicative_2401_, 3);
v_toSeqRight_2408_ = lean_ctor_get(v_toApplicative_2401_, 4);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_toApplicative_2401_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v_toApplicative_2401_, 1);
lean_dec(v_unused_2432_);
v___x_2410_ = v_toApplicative_2401_;
v_isShared_2411_ = v_isSharedCheck_2431_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_toSeqRight_2408_);
lean_inc(v_toSeqLeft_2407_);
lean_inc(v_toSeq_2406_);
lean_inc(v_toFunctor_2405_);
lean_dec(v_toApplicative_2401_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2431_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___f_2417_; lean_object* v___f_2418_; lean_object* v___f_2419_; lean_object* v___x_2421_; 
v___f_2412_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2413_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2405_);
v___f_2414_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2414_, 0, v_toFunctor_2405_);
v___f_2415_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2415_, 0, v_toFunctor_2405_);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___f_2414_);
lean_ctor_set(v___x_2416_, 1, v___f_2415_);
v___f_2417_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2417_, 0, v_toSeqRight_2408_);
v___f_2418_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2418_, 0, v_toSeqLeft_2407_);
v___f_2419_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2419_, 0, v_toSeq_2406_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v___f_2417_);
lean_ctor_set(v___x_2410_, 3, v___f_2418_);
lean_ctor_set(v___x_2410_, 2, v___f_2419_);
lean_ctor_set(v___x_2410_, 1, v___f_2412_);
lean_ctor_set(v___x_2410_, 0, v___x_2416_);
v___x_2421_ = v___x_2410_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v___f_2412_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v___f_2419_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v___f_2418_);
lean_ctor_set(v_reuseFailAlloc_2430_, 4, v___f_2417_);
v___x_2421_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v___f_2413_);
lean_ctor_set(v___x_2403_, 0, v___x_2421_);
v___x_2423_ = v___x_2403_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___f_2413_);
v___x_2423_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_27699__overap_2427_; lean_object* v___x_2428_; 
v___x_2424_ = l_StateRefT_x27_instMonad___redArg(v___x_2423_);
v___x_2425_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2426_ = l_instInhabitedOfMonad___redArg(v___x_2424_, v___x_2425_);
v___x_27699__overap_2427_ = lean_panic_fn_borrowed(v___x_2426_, v_msg_2377_);
lean_dec(v___x_2426_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
v___x_2428_ = lean_apply_6(v___x_27699__overap_2427_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, lean_box(0));
return v___x_2428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
return v_res_2442_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2443_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2447_ = lean_unsigned_to_nat(0u);
v___x_2448_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
lean_ctor_set(v___x_2448_, 2, v___x_2447_);
lean_ctor_set(v___x_2448_, 3, v___x_2447_);
lean_ctor_set(v___x_2448_, 4, v___x_2446_);
lean_ctor_set(v___x_2448_, 5, v___x_2446_);
lean_ctor_set(v___x_2448_, 6, v___x_2446_);
lean_ctor_set(v___x_2448_, 7, v___x_2446_);
lean_ctor_set(v___x_2448_, 8, v___x_2446_);
lean_ctor_set(v___x_2448_, 9, v___x_2446_);
lean_ctor_set(v___x_2448_, 10, v___x_2446_);
return v___x_2448_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = lean_unsigned_to_nat(32u);
v___x_2450_ = lean_mk_empty_array_with_capacity(v___x_2449_);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2452_ = ((size_t)5ULL);
v___x_2453_ = lean_unsigned_to_nat(0u);
v___x_2454_ = lean_unsigned_to_nat(32u);
v___x_2455_ = lean_mk_empty_array_with_capacity(v___x_2454_);
v___x_2456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2457_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
lean_ctor_set(v___x_2457_, 2, v___x_2453_);
lean_ctor_set(v___x_2457_, 3, v___x_2453_);
lean_ctor_set_usize(v___x_2457_, 4, v___x_2452_);
return v___x_2457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2458_ = lean_box(1);
v___x_2459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
lean_ctor_set(v___x_2461_, 1, v___x_2459_);
lean_ctor_set(v___x_2461_, 2, v___x_2458_);
return v___x_2461_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2464_ = l_Lean_stringToMessageData(v___x_2463_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2467_ = l_Lean_stringToMessageData(v___x_2466_);
return v___x_2467_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2470_ = l_Lean_stringToMessageData(v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2473_ = l_Lean_stringToMessageData(v___x_2472_);
return v___x_2473_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2476_ = l_Lean_stringToMessageData(v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2479_ = l_Lean_stringToMessageData(v___x_2478_);
return v___x_2479_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2482_ = l_Lean_stringToMessageData(v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2483_, lean_object* v_declHint_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v___x_2487_; lean_object* v_env_2488_; uint8_t v___x_2489_; 
v___x_2487_ = lean_st_ref_get(v___y_2485_);
v_env_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc_ref(v_env_2488_);
lean_dec(v___x_2487_);
v___x_2489_ = l_Lean_Name_isAnonymous(v_declHint_2484_);
if (v___x_2489_ == 0)
{
uint8_t v_isExporting_2490_; 
v_isExporting_2490_ = lean_ctor_get_uint8(v_env_2488_, sizeof(void*)*8);
if (v_isExporting_2490_ == 0)
{
lean_object* v___x_2491_; 
lean_dec_ref(v_env_2488_);
lean_dec(v_declHint_2484_);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_msg_2483_);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; uint8_t v___x_2493_; 
lean_inc_ref(v_env_2488_);
v___x_2492_ = l_Lean_Environment_setExporting(v_env_2488_, v___x_2489_);
lean_inc(v_declHint_2484_);
lean_inc_ref(v___x_2492_);
v___x_2493_ = l_Lean_Environment_contains(v___x_2492_, v_declHint_2484_, v_isExporting_2490_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref(v___x_2492_);
lean_dec_ref(v_env_2488_);
lean_dec(v_declHint_2484_);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v_msg_2483_);
return v___x_2494_;
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v_c_2500_; lean_object* v___x_2501_; 
v___x_2495_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2496_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2497_ = l_Lean_Options_empty;
v___x_2498_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2492_);
lean_ctor_set(v___x_2498_, 1, v___x_2495_);
lean_ctor_set(v___x_2498_, 2, v___x_2496_);
lean_ctor_set(v___x_2498_, 3, v___x_2497_);
lean_inc(v_declHint_2484_);
v___x_2499_ = l_Lean_MessageData_ofConstName(v_declHint_2484_, v___x_2489_);
v_c_2500_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2500_, 0, v___x_2498_);
lean_ctor_set(v_c_2500_, 1, v___x_2499_);
v___x_2501_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2488_, v_declHint_2484_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_dec_ref(v_env_2488_);
lean_dec(v_declHint_2484_);
v___x_2502_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v_c_2500_);
v___x_2504_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = l_Lean_MessageData_note(v___x_2505_);
v___x_2507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_msg_2483_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
else
{
lean_object* v_val_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2544_; 
v_val_2509_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2511_ = v___x_2501_;
v_isShared_2512_ = v_isSharedCheck_2544_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_val_2509_);
lean_dec(v___x_2501_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2544_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_mod_2516_; uint8_t v___x_2517_; 
v___x_2513_ = lean_box(0);
v___x_2514_ = l_Lean_Environment_header(v_env_2488_);
lean_dec_ref(v_env_2488_);
v___x_2515_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2514_);
v_mod_2516_ = lean_array_get(v___x_2513_, v___x_2515_, v_val_2509_);
lean_dec(v_val_2509_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = l_Lean_isPrivateName(v_declHint_2484_);
lean_dec(v_declHint_2484_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v_c_2500_);
v___x_2520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_Lean_MessageData_ofName(v_mod_2516_);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = l_Lean_MessageData_note(v___x_2525_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v_msg_2483_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2527_);
v___x_2529_ = v___x_2511_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2531_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v_c_2500_);
v___x_2533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = l_Lean_MessageData_ofName(v_mod_2516_);
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_MessageData_note(v___x_2538_);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v_msg_2483_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2540_);
v___x_2542_ = v___x_2511_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2545_; 
lean_dec_ref(v_env_2488_);
lean_dec(v_declHint_2484_);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_msg_2483_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2546_, lean_object* v_declHint_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2546_, v_declHint_2547_, v___y_2548_);
lean_dec(v___y_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2551_, lean_object* v_declHint_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2569_; 
v___x_2559_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2551_, v_declHint_2552_, v___y_2557_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2564_ = l_Lean_unknownIdentifierMessageTag;
v___x_2565_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v_a_2560_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2565_);
v___x_2567_ = v___x_2562_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2570_, lean_object* v_declHint_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2570_, v_declHint_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_ref_2585_; lean_object* v___x_2586_; lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2595_; 
v_ref_2585_ = lean_ctor_get(v___y_2582_, 5);
v___x_2586_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_inc(v_ref_2585_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_ref_2585_);
lean_ctor_set(v___x_2591_, 1, v_a_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 1);
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2603_, lean_object* v_msg_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_fileName_2611_; lean_object* v_fileMap_2612_; lean_object* v_options_2613_; lean_object* v_currRecDepth_2614_; lean_object* v_maxRecDepth_2615_; lean_object* v_ref_2616_; lean_object* v_currNamespace_2617_; lean_object* v_openDecls_2618_; lean_object* v_initHeartbeats_2619_; lean_object* v_maxHeartbeats_2620_; lean_object* v_quotContext_2621_; lean_object* v_currMacroScope_2622_; uint8_t v_diag_2623_; lean_object* v_cancelTk_x3f_2624_; uint8_t v_suppressElabErrors_2625_; lean_object* v_inheritedTraceOptions_2626_; lean_object* v_ref_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_fileName_2611_ = lean_ctor_get(v___y_2608_, 0);
v_fileMap_2612_ = lean_ctor_get(v___y_2608_, 1);
v_options_2613_ = lean_ctor_get(v___y_2608_, 2);
v_currRecDepth_2614_ = lean_ctor_get(v___y_2608_, 3);
v_maxRecDepth_2615_ = lean_ctor_get(v___y_2608_, 4);
v_ref_2616_ = lean_ctor_get(v___y_2608_, 5);
v_currNamespace_2617_ = lean_ctor_get(v___y_2608_, 6);
v_openDecls_2618_ = lean_ctor_get(v___y_2608_, 7);
v_initHeartbeats_2619_ = lean_ctor_get(v___y_2608_, 8);
v_maxHeartbeats_2620_ = lean_ctor_get(v___y_2608_, 9);
v_quotContext_2621_ = lean_ctor_get(v___y_2608_, 10);
v_currMacroScope_2622_ = lean_ctor_get(v___y_2608_, 11);
v_diag_2623_ = lean_ctor_get_uint8(v___y_2608_, sizeof(void*)*14);
v_cancelTk_x3f_2624_ = lean_ctor_get(v___y_2608_, 12);
v_suppressElabErrors_2625_ = lean_ctor_get_uint8(v___y_2608_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2626_ = lean_ctor_get(v___y_2608_, 13);
v_ref_2627_ = l_Lean_replaceRef(v_ref_2603_, v_ref_2616_);
lean_inc_ref(v_inheritedTraceOptions_2626_);
lean_inc(v_cancelTk_x3f_2624_);
lean_inc(v_currMacroScope_2622_);
lean_inc(v_quotContext_2621_);
lean_inc(v_maxHeartbeats_2620_);
lean_inc(v_initHeartbeats_2619_);
lean_inc(v_openDecls_2618_);
lean_inc(v_currNamespace_2617_);
lean_inc(v_maxRecDepth_2615_);
lean_inc(v_currRecDepth_2614_);
lean_inc_ref(v_options_2613_);
lean_inc_ref(v_fileMap_2612_);
lean_inc_ref(v_fileName_2611_);
v___x_2628_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2628_, 0, v_fileName_2611_);
lean_ctor_set(v___x_2628_, 1, v_fileMap_2612_);
lean_ctor_set(v___x_2628_, 2, v_options_2613_);
lean_ctor_set(v___x_2628_, 3, v_currRecDepth_2614_);
lean_ctor_set(v___x_2628_, 4, v_maxRecDepth_2615_);
lean_ctor_set(v___x_2628_, 5, v_ref_2627_);
lean_ctor_set(v___x_2628_, 6, v_currNamespace_2617_);
lean_ctor_set(v___x_2628_, 7, v_openDecls_2618_);
lean_ctor_set(v___x_2628_, 8, v_initHeartbeats_2619_);
lean_ctor_set(v___x_2628_, 9, v_maxHeartbeats_2620_);
lean_ctor_set(v___x_2628_, 10, v_quotContext_2621_);
lean_ctor_set(v___x_2628_, 11, v_currMacroScope_2622_);
lean_ctor_set(v___x_2628_, 12, v_cancelTk_x3f_2624_);
lean_ctor_set(v___x_2628_, 13, v_inheritedTraceOptions_2626_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*14, v_diag_2623_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*14 + 1, v_suppressElabErrors_2625_);
v___x_2629_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2604_, v___y_2606_, v___y_2607_, v___x_2628_, v___y_2609_);
lean_dec_ref_known(v___x_2628_, 14);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2630_, lean_object* v_msg_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2630_, v_msg_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec(v_ref_2630_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2639_, lean_object* v_msg_2640_, lean_object* v_declHint_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; lean_object* v_a_2649_; lean_object* v___x_2650_; 
v___x_2648_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2640_, v_declHint_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v___x_2648_);
v___x_2650_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2639_, v_a_2649_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2651_, lean_object* v_msg_2652_, lean_object* v_declHint_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2651_, v_msg_2652_, v_declHint_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec(v_ref_2651_);
return v_res_2660_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2663_ = l_Lean_stringToMessageData(v___x_2662_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2666_ = l_Lean_stringToMessageData(v___x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2667_, lean_object* v_constName_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2675_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2676_ = 0;
lean_inc(v_constName_2668_);
v___x_2677_ = l_Lean_MessageData_ofConstName(v_constName_2668_, v___x_2676_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2675_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2667_, v___x_2680_, v_constName_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2682_, lean_object* v_constName_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2682_, v_constName_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec(v_ref_2682_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_ref_2698_; lean_object* v___x_2699_; 
v_ref_2698_ = lean_ctor_get(v___y_2695_, 5);
v___x_2699_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2698_, v_constName_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; lean_object* v_env_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; 
v___x_2715_ = lean_st_ref_get(v___y_2713_);
v_env_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc_ref(v_env_2716_);
lean_dec(v___x_2715_);
v___x_2717_ = 0;
lean_inc(v_constName_2708_);
v___x_2718_ = l_Lean_Environment_find_x3f(v_env_2716_, v_constName_2708_, v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
return v___x_2719_;
}
else
{
lean_object* v_val_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_constName_2708_);
v_val_2720_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2718_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_val_2720_);
lean_dec(v___x_2718_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 0);
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_val_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
return v_res_2735_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2740_ = lean_unsigned_to_nat(53u);
v___x_2741_ = lean_unsigned_to_nat(62u);
v___x_2742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2744_ = l_mkPanicMessageWithDecl(v___x_2743_, v___x_2742_, v___x_2741_, v___x_2740_, v___x_2739_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2745_, size_t v_i_2746_, lean_object* v_bs_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_usize_dec_lt(v_i_2746_, v_sz_2745_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_bs_2747_);
return v___x_2755_;
}
else
{
lean_object* v_v_2756_; lean_object* v___x_2757_; 
v_v_2756_ = lean_array_uget_borrowed(v_bs_2747_, v_i_2746_);
lean_inc(v_v_2756_);
v___x_2757_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2756_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2759_; lean_object* v_bs_x27_2760_; lean_object* v_a_2762_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2757_, 1);
v___x_2759_ = lean_unsigned_to_nat(0u);
v_bs_x27_2760_ = lean_array_uset(v_bs_2747_, v_i_2746_, v___x_2759_);
if (lean_obj_tag(v_a_2758_) == 6)
{
lean_object* v_val_2767_; lean_object* v_numFields_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; 
v_val_2767_ = lean_ctor_get(v_a_2758_, 0);
lean_inc_ref(v_val_2767_);
lean_dec_ref_known(v_a_2758_, 1);
v_numFields_2768_ = lean_ctor_get(v_val_2767_, 4);
lean_inc(v_numFields_2768_);
lean_dec_ref(v_val_2767_);
v___x_2769_ = 0;
v___x_2770_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2770_, 0, v_numFields_2768_);
lean_ctor_set(v___x_2770_, 1, v___x_2759_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*2, v___x_2769_);
v_a_2762_ = v___x_2770_;
goto v___jp_2761_;
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec(v_a_2758_);
v___x_2771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2772_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2771_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v_a_2762_ = v_a_2773_;
goto v___jp_2761_;
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref(v_bs_x27_2760_);
v_a_2774_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2772_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2772_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
v___jp_2761_:
{
size_t v___x_2763_; size_t v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = ((size_t)1ULL);
v___x_2764_ = lean_usize_add(v_i_2746_, v___x_2763_);
v___x_2765_ = lean_array_uset(v_bs_x27_2760_, v_i_2746_, v_a_2762_);
v_i_2746_ = v___x_2764_;
v_bs_2747_ = v___x_2765_;
goto _start;
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec_ref(v_bs_2747_);
v_a_2782_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2757_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2757_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2790_, lean_object* v_i_2791_, lean_object* v_bs_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
size_t v_sz_boxed_2799_; size_t v_i_boxed_2800_; lean_object* v_res_2801_; 
v_sz_boxed_2799_ = lean_unbox_usize(v_sz_2790_);
lean_dec(v_sz_2790_);
v_i_boxed_2800_ = lean_unbox_usize(v_i_2791_);
lean_dec(v_i_2791_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2799_, v_i_boxed_2800_, v_bs_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
return v_res_2801_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v_cellCount_2802_; lean_object* v___x_2803_; 
v_cellCount_2802_ = lean_unsigned_to_nat(16u);
v___x_2803_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2802_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v_cellCount_2804_; lean_object* v___x_2805_; 
v_cellCount_2804_ = lean_unsigned_to_nat(16u);
v___x_2805_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2804_);
return v___x_2805_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2806_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2807_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2808_ = lean_unsigned_to_nat(0u);
v___x_2809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v___x_2807_);
lean_ctor_set(v___x_2809_, 2, v___x_2806_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2812_, uint8_t v_alsoCasesOn_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = l_Lean_Expr_isApp(v_e_2812_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v_e_2812_);
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
else
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_Expr_getAppFn(v_e_2812_);
if (lean_obj_tag(v___x_2826_) == 4)
{
lean_object* v_declName_2827_; lean_object* v_us_2828_; lean_object* v___x_2829_; lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2984_; 
v_declName_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc_n(v_declName_2827_, 2);
v_us_2828_ = lean_ctor_get(v___x_2826_, 1);
lean_inc(v_us_2828_);
lean_dec_ref_known(v___x_2826_, 2);
v___x_2829_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2827_, v___y_2818_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2984_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2984_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
if (lean_obj_tag(v_a_2830_) == 1)
{
lean_object* v_val_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2876_; 
v_val_2834_ = lean_ctor_get(v_a_2830_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_a_2830_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2836_ = v_a_2830_;
v_isShared_2837_ = v_isSharedCheck_2876_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_val_2834_);
lean_dec(v_a_2830_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2876_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v_dummy_2838_; lean_object* v_nargs_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v_args_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v_dummy_2838_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2839_ = l_Lean_Expr_getAppNumArgs(v_e_2812_);
lean_inc(v_nargs_2839_);
v___x_2840_ = lean_mk_array(v_nargs_2839_, v_dummy_2838_);
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = lean_nat_sub(v_nargs_2839_, v___x_2841_);
lean_dec(v_nargs_2839_);
v_args_2843_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2812_, v___x_2840_, v___x_2842_);
v___x_2844_ = lean_array_get_size(v_args_2843_);
v___x_2845_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2834_);
v___x_2846_ = lean_nat_dec_lt(v___x_2844_, v___x_2845_);
lean_dec(v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v_numParams_2847_; lean_object* v_numDiscrs_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v_numParams_2847_ = lean_ctor_get(v_val_2834_, 0);
v_numDiscrs_2848_ = lean_ctor_get(v_val_2834_, 1);
v___x_2849_ = lean_array_mk(v_us_2828_);
v___x_2850_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2847_);
v___x_2851_ = l_Array_extract___redArg(v_args_2843_, v___x_2850_, v_numParams_2847_);
v___x_2852_ = l_Lean_instInhabitedExpr;
v___x_2853_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2834_);
v___x_2854_ = lean_array_get(v___x_2852_, v_args_2843_, v___x_2853_);
lean_dec(v___x_2853_);
v___x_2855_ = lean_nat_add(v_numParams_2847_, v___x_2841_);
v___x_2856_ = lean_nat_add(v___x_2855_, v_numDiscrs_2848_);
lean_inc(v___x_2856_);
lean_inc_ref_n(v_args_2843_, 2);
v___x_2857_ = l_Array_toSubarray___redArg(v_args_2843_, v___x_2855_, v___x_2856_);
v___x_2858_ = l_Subarray_copy___redArg(v___x_2857_);
v___x_2859_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2834_);
v___x_2860_ = lean_nat_add(v___x_2856_, v___x_2859_);
lean_dec(v___x_2859_);
lean_inc(v___x_2860_);
v___x_2861_ = l_Array_toSubarray___redArg(v_args_2843_, v___x_2856_, v___x_2860_);
v___x_2862_ = l_Subarray_copy___redArg(v___x_2861_);
v___x_2863_ = l_Array_toSubarray___redArg(v_args_2843_, v___x_2860_, v___x_2844_);
v___x_2864_ = l_Subarray_copy___redArg(v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2865_, 0, v_val_2834_);
lean_ctor_set(v___x_2865_, 1, v_declName_2827_);
lean_ctor_set(v___x_2865_, 2, v___x_2849_);
lean_ctor_set(v___x_2865_, 3, v___x_2851_);
lean_ctor_set(v___x_2865_, 4, v___x_2854_);
lean_ctor_set(v___x_2865_, 5, v___x_2858_);
lean_ctor_set(v___x_2865_, 6, v___x_2862_);
lean_ctor_set(v___x_2865_, 7, v___x_2864_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2865_);
v___x_2867_ = v___x_2836_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2867_);
v___x_2869_ = v___x_2832_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
lean_dec_ref(v_args_2843_);
lean_del_object(v___x_2836_);
lean_dec(v_val_2834_);
lean_dec(v_us_2828_);
lean_dec(v_declName_2827_);
v___x_2872_ = lean_box(0);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2872_);
v___x_2874_ = v___x_2832_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_object* v___x_2877_; 
lean_del_object(v___x_2832_);
lean_dec(v_a_2830_);
v___x_2877_ = lean_st_ref_get(v___y_2818_);
if (v_alsoCasesOn_2813_ == 0)
{
lean_dec(v___x_2877_);
lean_dec(v_us_2828_);
lean_dec(v_declName_2827_);
lean_dec_ref(v_e_2812_);
goto v___jp_2820_;
}
else
{
lean_object* v_env_2878_; uint8_t v___x_2879_; 
v_env_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc_ref(v_env_2878_);
lean_dec(v___x_2877_);
lean_inc(v_declName_2827_);
v___x_2879_ = l_Lean_isCasesOnRecursor(v_env_2878_, v_declName_2827_);
if (v___x_2879_ == 0)
{
lean_dec(v_us_2828_);
lean_dec(v_declName_2827_);
lean_dec_ref(v_e_2812_);
goto v___jp_2820_;
}
else
{
lean_object* v_indName_2880_; lean_object* v___x_2881_; 
v_indName_2880_ = l_Lean_Name_getPrefix(v_declName_2827_);
v___x_2881_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2880_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2975_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2975_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2975_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
if (lean_obj_tag(v_a_2882_) == 5)
{
lean_object* v_val_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2970_; 
v_val_2886_ = lean_ctor_get(v_a_2882_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_a_2882_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2888_ = v_a_2882_;
v_isShared_2889_ = v_isSharedCheck_2970_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_val_2886_);
lean_dec(v_a_2882_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2970_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v_toConstantVal_2890_; lean_object* v_numParams_2891_; lean_object* v_numIndices_2892_; lean_object* v_ctors_2893_; lean_object* v_nargs_2894_; lean_object* v_dummy_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v_args_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v_toConstantVal_2890_ = lean_ctor_get(v_val_2886_, 0);
lean_inc_ref(v_toConstantVal_2890_);
v_numParams_2891_ = lean_ctor_get(v_val_2886_, 1);
lean_inc(v_numParams_2891_);
v_numIndices_2892_ = lean_ctor_get(v_val_2886_, 2);
lean_inc(v_numIndices_2892_);
v_ctors_2893_ = lean_ctor_get(v_val_2886_, 4);
lean_inc(v_ctors_2893_);
v_nargs_2894_ = l_Lean_Expr_getAppNumArgs(v_e_2812_);
v_dummy_2895_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2894_);
v___x_2896_ = lean_mk_array(v_nargs_2894_, v_dummy_2895_);
v___x_2897_ = lean_unsigned_to_nat(1u);
v___x_2898_ = lean_nat_sub(v_nargs_2894_, v___x_2897_);
lean_dec(v_nargs_2894_);
v_args_2899_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2812_, v___x_2896_, v___x_2898_);
v___x_2900_ = lean_nat_add(v_numParams_2891_, v___x_2897_);
v___x_2901_ = lean_nat_add(v___x_2900_, v_numIndices_2892_);
v___x_2902_ = lean_nat_add(v___x_2901_, v___x_2897_);
lean_dec(v___x_2901_);
v___x_2903_ = l_Lean_InductiveVal_numCtors(v_val_2886_);
lean_dec_ref(v_val_2886_);
v___x_2904_ = lean_nat_add(v___x_2902_, v___x_2903_);
lean_dec(v___x_2903_);
v___x_2905_ = lean_array_get_size(v_args_2899_);
v___x_2906_ = lean_nat_dec_le(v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_dec(v___x_2904_);
lean_dec(v___x_2902_);
lean_dec(v___x_2900_);
lean_dec_ref(v_args_2899_);
lean_dec(v_ctors_2893_);
lean_dec(v_numIndices_2892_);
lean_dec(v_numParams_2891_);
lean_dec_ref(v_toConstantVal_2890_);
lean_del_object(v___x_2888_);
lean_dec(v_us_2828_);
lean_dec(v_declName_2827_);
v___x_2907_ = lean_box(0);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2907_);
v___x_2909_ = v___x_2884_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
else
{
lean_object* v___x_2911_; lean_object* v_params_2912_; lean_object* v___x_2913_; lean_object* v_motive_2914_; lean_object* v_discrs_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v_discrInfos_2918_; lean_object* v_alts_2919_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v_lower_2961_; lean_object* v_upper_2962_; uint8_t v___x_2969_; 
lean_del_object(v___x_2884_);
v___x_2911_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2891_);
lean_inc_ref_n(v_args_2899_, 3);
v_params_2912_ = l_Array_toSubarray___redArg(v_args_2899_, v___x_2911_, v_numParams_2891_);
v___x_2913_ = l_Lean_instInhabitedExpr;
v_motive_2914_ = lean_array_get(v___x_2913_, v_args_2899_, v_numParams_2891_);
lean_dec(v_numParams_2891_);
lean_inc(v___x_2902_);
v_discrs_2915_ = l_Array_toSubarray___redArg(v_args_2899_, v___x_2900_, v___x_2902_);
v___x_2916_ = lean_nat_add(v_numIndices_2892_, v___x_2897_);
lean_dec(v_numIndices_2892_);
v___x_2917_ = lean_box(0);
v_discrInfos_2918_ = lean_mk_array(v___x_2916_, v___x_2917_);
lean_inc(v___x_2904_);
v_alts_2919_ = l_Array_toSubarray___redArg(v_args_2899_, v___x_2902_, v___x_2904_);
v___x_2969_ = lean_nat_dec_le(v___x_2904_, v___x_2911_);
if (v___x_2969_ == 0)
{
v_lower_2961_ = v___x_2904_;
v_upper_2962_ = v___x_2905_;
goto v___jp_2960_;
}
else
{
lean_dec(v___x_2904_);
v_lower_2961_ = v___x_2911_;
v_upper_2962_ = v___x_2905_;
goto v___jp_2960_;
}
v___jp_2920_:
{
lean_object* v___x_2923_; size_t v_sz_2924_; size_t v___x_2925_; lean_object* v___x_2926_; 
v___x_2923_ = lean_array_mk(v_ctors_2893_);
v_sz_2924_ = lean_array_size(v___x_2923_);
v___x_2925_ = ((size_t)0ULL);
v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2924_, v___x_2925_, v___x_2923_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2951_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2951_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2951_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v_start_2931_; lean_object* v_stop_2932_; lean_object* v_start_2933_; lean_object* v_stop_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2946_; 
v_start_2931_ = lean_ctor_get(v_params_2912_, 1);
lean_inc(v_start_2931_);
v_stop_2932_ = lean_ctor_get(v_params_2912_, 2);
lean_inc(v_stop_2932_);
v_start_2933_ = lean_ctor_get(v_discrs_2915_, 1);
lean_inc(v_start_2933_);
v_stop_2934_ = lean_ctor_get(v_discrs_2915_, 2);
lean_inc(v_stop_2934_);
v___x_2935_ = lean_nat_sub(v_stop_2932_, v_start_2931_);
lean_dec(v_start_2931_);
lean_dec(v_stop_2932_);
v___x_2936_ = lean_nat_sub(v_stop_2934_, v_start_2933_);
lean_dec(v_start_2933_);
lean_dec(v_stop_2934_);
v___x_2937_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2);
v___x_2938_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2935_);
lean_ctor_set(v___x_2938_, 1, v___x_2936_);
lean_ctor_set(v___x_2938_, 2, v_a_2927_);
lean_ctor_set(v___x_2938_, 3, v___y_2922_);
lean_ctor_set(v___x_2938_, 4, v_discrInfos_2918_);
lean_ctor_set(v___x_2938_, 5, v___x_2937_);
v___x_2939_ = lean_array_mk(v_us_2828_);
v___x_2940_ = l_Subarray_copy___redArg(v_params_2912_);
v___x_2941_ = l_Subarray_copy___redArg(v_discrs_2915_);
v___x_2942_ = l_Subarray_copy___redArg(v_alts_2919_);
v___x_2943_ = l_Subarray_copy___redArg(v___y_2921_);
v___x_2944_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2938_);
lean_ctor_set(v___x_2944_, 1, v_declName_2827_);
lean_ctor_set(v___x_2944_, 2, v___x_2939_);
lean_ctor_set(v___x_2944_, 3, v___x_2940_);
lean_ctor_set(v___x_2944_, 4, v_motive_2914_);
lean_ctor_set(v___x_2944_, 5, v___x_2941_);
lean_ctor_set(v___x_2944_, 6, v___x_2942_);
lean_ctor_set(v___x_2944_, 7, v___x_2943_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set_tag(v___x_2888_, 1);
lean_ctor_set(v___x_2888_, 0, v___x_2944_);
v___x_2946_ = v___x_2888_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2948_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2946_);
v___x_2948_ = v___x_2929_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v_alts_2919_);
lean_dec_ref(v_discrInfos_2918_);
lean_dec_ref(v_discrs_2915_);
lean_dec(v_motive_2914_);
lean_dec_ref(v_params_2912_);
lean_del_object(v___x_2888_);
lean_dec(v_us_2828_);
lean_dec(v_declName_2827_);
v_a_2952_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2926_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2926_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
v___jp_2960_:
{
lean_object* v_levelParams_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v_levelParams_2963_ = lean_ctor_get(v_toConstantVal_2890_, 1);
lean_inc(v_levelParams_2963_);
lean_dec_ref(v_toConstantVal_2890_);
v___x_2964_ = l_Array_toSubarray___redArg(v_args_2899_, v_lower_2961_, v_upper_2962_);
v___x_2965_ = l_List_lengthTR___redArg(v_levelParams_2963_);
lean_dec(v_levelParams_2963_);
v___x_2966_ = l_List_lengthTR___redArg(v_us_2828_);
v___x_2967_ = lean_nat_dec_eq(v___x_2965_, v___x_2966_);
lean_dec(v___x_2966_);
lean_dec(v___x_2965_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
v___x_2968_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__3));
v___y_2921_ = v___x_2964_;
v___y_2922_ = v___x_2968_;
goto v___jp_2920_;
}
else
{
v___y_2921_ = v___x_2964_;
v___y_2922_ = v___x_2917_;
goto v___jp_2920_;
}
}
}
}
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
lean_dec(v_a_2882_);
lean_dec(v_us_2828_);
lean_dec(v_declName_2827_);
lean_dec_ref(v_e_2812_);
v___x_2971_ = lean_box(0);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2971_);
v___x_2973_ = v___x_2884_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_us_2828_);
lean_dec(v_declName_2827_);
lean_dec_ref(v_e_2812_);
v_a_2976_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2881_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2881_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2826_);
lean_dec_ref(v_e_2812_);
goto v___jp_2820_;
}
}
v___jp_2820_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = lean_box(0);
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2985_, lean_object* v_alsoCasesOn_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2993_; lean_object* v_res_2994_; 
v_alsoCasesOn_boxed_2993_ = lean_unbox(v_alsoCasesOn_2986_);
v_res_2994_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2985_, v_alsoCasesOn_boxed_2993_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
if (lean_obj_tag(v_a_2995_) == 0)
{
lean_object* v___x_2997_; 
v___x_2997_ = l_List_reverse___redArg(v_a_2996_);
return v___x_2997_;
}
else
{
lean_object* v_head_2998_; lean_object* v_tail_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3008_; 
v_head_2998_ = lean_ctor_get(v_a_2995_, 0);
v_tail_2999_ = lean_ctor_get(v_a_2995_, 1);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_a_2995_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3001_ = v_a_2995_;
v_isShared_3002_ = v_isSharedCheck_3008_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_tail_2999_);
lean_inc(v_head_2998_);
lean_dec(v_a_2995_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3008_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3003_ = l_Lean_MessageData_ofExpr(v_head_2998_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v_a_2996_);
lean_ctor_set(v___x_3001_, 0, v___x_3003_);
v___x_3005_ = v___x_3001_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_a_2996_);
v___x_3005_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
v_a_2995_ = v_tail_2999_;
v_a_2996_ = v___x_3005_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_3009_, lean_object* v_x_3010_){
_start:
{
lean_object* v_fnName_3011_; uint8_t v___x_3012_; 
v_fnName_3011_ = lean_ctor_get(v_x_3010_, 0);
v___x_3012_ = l_Lean_Expr_isConstOf(v_x_3009_, v_fnName_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_3013_, lean_object* v_x_3014_){
_start:
{
uint8_t v_res_3015_; lean_object* v_r_3016_; 
v_res_3015_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_3013_, v_x_3014_);
lean_dec_ref(v_x_3014_);
lean_dec_ref(v_x_3013_);
v_r_3016_ = lean_box(v_res_3015_);
return v_r_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_3017_, lean_object* v_positions_3018_, lean_object* v_recFnNames_3019_, lean_object* v_containsRecFn_3020_, lean_object* v_below_3021_, size_t v_sz_3022_, size_t v_i_3023_, lean_object* v_bs_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_usize_dec_lt(v_i_3023_, v_sz_3022_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; 
lean_dec_ref(v_below_3021_);
lean_dec_ref(v_containsRecFn_3020_);
lean_dec_ref(v_recFnNames_3019_);
lean_dec_ref(v_positions_3018_);
lean_dec_ref(v_recArgInfos_3017_);
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_bs_3024_);
return v___x_3032_;
}
else
{
lean_object* v_v_3033_; lean_object* v___x_3034_; 
v_v_3033_ = lean_array_uget_borrowed(v_bs_3024_, v_i_3023_);
lean_inc_ref(v___y_3028_);
lean_inc(v_v_3033_);
lean_inc_ref(v_below_3021_);
lean_inc_ref(v_containsRecFn_3020_);
lean_inc_ref(v_recFnNames_3019_);
lean_inc_ref(v_positions_3018_);
lean_inc_ref(v_recArgInfos_3017_);
v___x_3034_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3017_, v_positions_3018_, v_recFnNames_3019_, v_containsRecFn_3020_, v_below_3021_, v_v_3033_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3036_; lean_object* v_bs_x27_3037_; size_t v___x_3038_; size_t v___x_3039_; lean_object* v___x_3040_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v___x_3036_ = lean_unsigned_to_nat(0u);
v_bs_x27_3037_ = lean_array_uset(v_bs_3024_, v_i_3023_, v___x_3036_);
v___x_3038_ = ((size_t)1ULL);
v___x_3039_ = lean_usize_add(v_i_3023_, v___x_3038_);
v___x_3040_ = lean_array_uset(v_bs_x27_3037_, v_i_3023_, v_a_3035_);
v_i_3023_ = v___x_3039_;
v_bs_3024_ = v___x_3040_;
goto _start;
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec_ref(v_bs_3024_);
lean_dec_ref(v_below_3021_);
lean_dec_ref(v_containsRecFn_3020_);
lean_dec_ref(v_recFnNames_3019_);
lean_dec_ref(v_positions_3018_);
lean_dec_ref(v_recArgInfos_3017_);
v_a_3042_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3034_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3034_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3052_ = l_Lean_stringToMessageData(v___x_3051_);
return v___x_3052_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3055_ = l_Lean_stringToMessageData(v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3056_, lean_object* v_positions_3057_, lean_object* v_recFnNames_3058_, lean_object* v_containsRecFn_3059_, lean_object* v_below_3060_, lean_object* v_e_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_, lean_object* v_x_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
if (lean_obj_tag(v_x_3062_) == 5)
{
lean_object* v_fn_3071_; lean_object* v_arg_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_fn_3071_ = lean_ctor_get(v_x_3062_, 0);
lean_inc_ref(v_fn_3071_);
v_arg_3072_ = lean_ctor_get(v_x_3062_, 1);
lean_inc_ref(v_arg_3072_);
lean_dec_ref_known(v_x_3062_, 2);
v___x_3073_ = lean_array_set(v_x_3063_, v_x_3064_, v_arg_3072_);
v___x_3074_ = lean_unsigned_to_nat(1u);
v___x_3075_ = lean_nat_sub(v_x_3064_, v___x_3074_);
lean_dec(v_x_3064_);
v_x_3062_ = v_fn_3071_;
v_x_3063_ = v___x_3073_;
v_x_3064_ = v___x_3075_;
goto _start;
}
else
{
lean_object* v___f_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec(v_x_3064_);
lean_inc_ref(v_x_3062_);
v___f_3077_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3077_, 0, v_x_3062_);
v___x_3078_ = lean_unsigned_to_nat(0u);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3077_, v_recArgInfos_3056_, v___x_3078_);
if (lean_obj_tag(v___x_3079_) == 1)
{
lean_object* v_val_3080_; lean_object* v___x_3081_; lean_object* v___y_3083_; lean_object* v_recArgPos_3109_; lean_object* v_indGroupInst_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
lean_dec_ref(v_x_3062_);
v_val_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_val_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3081_ = lean_array_fget_borrowed(v_recArgInfos_3056_, v_val_3080_);
v_recArgPos_3109_ = lean_ctor_get(v___x_3081_, 2);
v_indGroupInst_3110_ = lean_ctor_get(v___x_3081_, 4);
v___x_3111_ = lean_array_get_size(v_x_3063_);
v___x_3112_ = lean_nat_dec_lt(v_recArgPos_3109_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec(v_val_3080_);
lean_dec_ref(v_x_3063_);
lean_dec_ref(v_below_3060_);
lean_dec_ref(v_containsRecFn_3059_);
lean_dec_ref(v_recFnNames_3058_);
lean_dec_ref(v_positions_3057_);
lean_dec_ref(v_recArgInfos_3056_);
v___x_3113_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3114_ = l_Lean_indentExpr(v_e_3061_);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3115_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_array_fget_borrowed(v_x_3063_, v_recArgPos_3109_);
lean_inc_ref(v___y_3068_);
lean_inc(v___x_3117_);
lean_inc_ref(v_below_3060_);
lean_inc_ref(v_containsRecFn_3059_);
lean_inc_ref(v_recFnNames_3058_);
lean_inc_ref(v_positions_3057_);
lean_inc_ref(v_recArgInfos_3056_);
v___x_3118_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3056_, v_positions_3057_, v_recFnNames_3058_, v_containsRecFn_3059_, v_below_3060_, v___x_3117_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v_params_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v_params_3120_ = lean_ctor_get(v_indGroupInst_3110_, 2);
v___x_3121_ = lean_array_get_size(v_params_3120_);
lean_inc_ref(v_positions_3057_);
lean_inc_ref(v_below_3060_);
v___x_3122_ = l_Lean_Elab_Structural_toBelow(v_below_3060_, v___x_3121_, v_positions_3057_, v_val_3080_, v_a_3119_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_dec_ref(v_e_3061_);
v___y_3083_ = v___x_3122_;
goto v___jp_3082_;
}
else
{
lean_object* v_a_3123_; uint8_t v___y_3125_; uint8_t v___x_3130_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
v___x_3130_ = l_Lean_Exception_isInterrupt(v_a_3123_);
if (v___x_3130_ == 0)
{
uint8_t v___x_3131_; 
v___x_3131_ = l_Lean_Exception_isRuntime(v_a_3123_);
v___y_3125_ = v___x_3131_;
goto v___jp_3124_;
}
else
{
lean_dec(v_a_3123_);
v___y_3125_ = v___x_3130_;
goto v___jp_3124_;
}
v___jp_3124_:
{
if (v___y_3125_ == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_dec_ref_known(v___x_3122_, 1);
v___x_3126_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3127_ = l_Lean_indentExpr(v_e_3061_);
v___x_3128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3126_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3128_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
v___y_3083_ = v___x_3129_;
goto v___jp_3082_;
}
else
{
lean_dec_ref(v_e_3061_);
v___y_3083_ = v___x_3122_;
goto v___jp_3082_;
}
}
}
}
else
{
lean_dec(v_val_3080_);
lean_dec_ref(v_x_3063_);
lean_dec_ref(v_e_3061_);
lean_dec_ref(v_below_3060_);
lean_dec_ref(v_containsRecFn_3059_);
lean_dec_ref(v_recFnNames_3058_);
lean_dec_ref(v_positions_3057_);
lean_dec_ref(v_recArgInfos_3056_);
return v___x_3118_;
}
}
v___jp_3082_:
{
if (lean_obj_tag(v___y_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_fixedParamPerm_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v_snd_3088_; size_t v_sz_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
v_a_3084_ = lean_ctor_get(v___y_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___y_3083_, 1);
v_fixedParamPerm_3085_ = lean_ctor_get(v___x_3081_, 1);
v___x_3086_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3085_, v_x_3063_);
lean_dec_ref(v_x_3063_);
lean_inc(v___x_3081_);
v___x_3087_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3081_, v___x_3086_);
v_snd_3088_ = lean_ctor_get(v___x_3087_, 1);
lean_inc(v_snd_3088_);
lean_dec_ref(v___x_3087_);
v_sz_3089_ = lean_array_size(v_snd_3088_);
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3056_, v_positions_3057_, v_recFnNames_3058_, v_containsRecFn_3059_, v_below_3060_, v_sz_3089_, v___x_3090_, v_snd_3088_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3100_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3100_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3100_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3096_ = l_Lean_mkAppN(v_a_3084_, v_a_3092_);
lean_dec(v_a_3092_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3096_);
v___x_3098_ = v___x_3094_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec(v_a_3084_);
v_a_3101_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3091_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3091_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_dec_ref(v_x_3063_);
lean_dec_ref(v_below_3060_);
lean_dec_ref(v_containsRecFn_3059_);
lean_dec_ref(v_recFnNames_3058_);
lean_dec_ref(v_positions_3057_);
lean_dec_ref(v_recArgInfos_3056_);
return v___y_3083_;
}
}
}
else
{
lean_object* v___x_3132_; 
lean_dec(v___x_3079_);
lean_dec_ref(v_e_3061_);
lean_inc_ref(v___y_3068_);
lean_inc_ref(v_below_3060_);
lean_inc_ref(v_containsRecFn_3059_);
lean_inc_ref(v_recFnNames_3058_);
lean_inc_ref(v_positions_3057_);
lean_inc_ref(v_recArgInfos_3056_);
v___x_3132_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3056_, v_positions_3057_, v_recFnNames_3058_, v_containsRecFn_3059_, v_below_3060_, v_x_3062_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; size_t v_sz_3134_; size_t v___x_3135_; lean_object* v___x_3136_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v_sz_3134_ = lean_array_size(v_x_3063_);
v___x_3135_ = ((size_t)0ULL);
v___x_3136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3056_, v_positions_3057_, v_recFnNames_3058_, v_containsRecFn_3059_, v_below_3060_, v_sz_3134_, v___x_3135_, v_x_3063_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3145_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3145_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3145_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = l_Lean_mkAppN(v_a_3133_, v_a_3137_);
lean_dec(v_a_3137_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3141_);
v___x_3143_ = v___x_3139_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_a_3133_);
v_a_3146_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3136_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3136_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_dec_ref(v_x_3063_);
lean_dec_ref(v_below_3060_);
lean_dec_ref(v_containsRecFn_3059_);
lean_dec_ref(v_recFnNames_3058_);
lean_dec_ref(v_positions_3057_);
lean_dec_ref(v_recArgInfos_3056_);
return v___x_3132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3154_, lean_object* v_recArgInfos_3155_, lean_object* v_positions_3156_, lean_object* v_recFnNames_3157_, lean_object* v_containsRecFn_3158_, lean_object* v_below_3159_, uint8_t v___x_3160_, uint8_t v_a_3161_, lean_object* v_x_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_expr_instantiate1(v_body_3154_, v_x_3162_);
lean_inc_ref(v___y_3166_);
v___x_3170_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3155_, v_positions_3156_, v_recFnNames_3157_, v_containsRecFn_3158_, v_below_3159_, v___x_3169_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; lean_object* v___x_3176_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___x_3170_, 1);
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3173_ = lean_mk_empty_array_with_capacity(v___x_3172_);
v___x_3174_ = lean_array_push(v___x_3173_, v_x_3162_);
v___x_3175_ = 1;
v___x_3176_ = l_Lean_Meta_mkLambdaFVars(v___x_3174_, v_a_3171_, v___x_3160_, v_a_3161_, v___x_3160_, v_a_3161_, v___x_3175_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec_ref(v___x_3174_);
return v___x_3176_;
}
else
{
lean_dec_ref(v_x_3162_);
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3177_, lean_object* v_recArgInfos_3178_, lean_object* v_positions_3179_, lean_object* v_recFnNames_3180_, lean_object* v_containsRecFn_3181_, lean_object* v_below_3182_, lean_object* v___x_3183_, lean_object* v_a_3184_, lean_object* v_x_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
uint8_t v___x_32919__boxed_3192_; uint8_t v_a_32920__boxed_3193_; lean_object* v_res_3194_; 
v___x_32919__boxed_3192_ = lean_unbox(v___x_3183_);
v_a_32920__boxed_3193_ = lean_unbox(v_a_3184_);
v_res_3194_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3177_, v_recArgInfos_3178_, v_positions_3179_, v_recFnNames_3180_, v_containsRecFn_3181_, v_below_3182_, v___x_32919__boxed_3192_, v_a_32920__boxed_3193_, v_x_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v_body_3177_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3195_, lean_object* v_recArgInfos_3196_, lean_object* v_positions_3197_, lean_object* v_recFnNames_3198_, lean_object* v_containsRecFn_3199_, lean_object* v_below_3200_, uint8_t v___x_3201_, uint8_t v_a_3202_, lean_object* v_x_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_expr_instantiate1(v_body_3195_, v_x_3203_);
lean_inc_ref(v___y_3207_);
v___x_3211_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3196_, v_positions_3197_, v_recFnNames_3198_, v_containsRecFn_3199_, v_below_3200_, v___x_3210_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_mk_empty_array_with_capacity(v___x_3213_);
v___x_3215_ = lean_array_push(v___x_3214_, v_x_3203_);
v___x_3216_ = 1;
v___x_3217_ = l_Lean_Meta_mkForallFVars(v___x_3215_, v_a_3212_, v___x_3201_, v_a_3202_, v_a_3202_, v___x_3216_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec_ref(v___x_3215_);
return v___x_3217_;
}
else
{
lean_dec_ref(v_x_3203_);
return v___x_3211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3218_, lean_object* v_recArgInfos_3219_, lean_object* v_positions_3220_, lean_object* v_recFnNames_3221_, lean_object* v_containsRecFn_3222_, lean_object* v_below_3223_, lean_object* v___x_3224_, lean_object* v_a_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
uint8_t v___x_32937__boxed_3233_; uint8_t v_a_32938__boxed_3234_; lean_object* v_res_3235_; 
v___x_32937__boxed_3233_ = lean_unbox(v___x_3224_);
v_a_32938__boxed_3234_ = lean_unbox(v_a_3225_);
v_res_3235_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3218_, v_recArgInfos_3219_, v_positions_3220_, v_recFnNames_3221_, v_containsRecFn_3222_, v_below_3223_, v___x_32937__boxed_3233_, v_a_32938__boxed_3234_, v_x_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v_body_3218_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3236_, lean_object* v_recArgInfos_3237_, lean_object* v_positions_3238_, lean_object* v_recFnNames_3239_, lean_object* v_containsRecFn_3240_, lean_object* v_below_3241_, lean_object* v_x_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3236_, v_recArgInfos_3237_, v_positions_3238_, v_recFnNames_3239_, v_containsRecFn_3240_, v_below_3241_, v_x_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v_x_3242_);
lean_dec_ref(v_body_3236_);
return v_res_3249_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3254_ = l_Lean_stringToMessageData(v___x_3253_);
return v___x_3254_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3257_ = l_Lean_stringToMessageData(v___x_3256_);
return v___x_3257_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3260_ = l_Lean_stringToMessageData(v___x_3259_);
return v___x_3260_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3263_ = l_Lean_stringToMessageData(v___x_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v_b_3264_, lean_object* v_recArgInfos_3265_, lean_object* v_positions_3266_, lean_object* v_recFnNames_3267_, lean_object* v_containsRecFn_3268_, uint8_t v___x_3269_, uint8_t v_a_3270_, lean_object* v___x_3271_, lean_object* v_a_3272_, lean_object* v_e_3273_, lean_object* v___x_3274_, lean_object* v_xs_3275_, lean_object* v_altBody_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v_options_3319_; uint8_t v_hasTrace_3320_; 
v_options_3319_ = lean_ctor_get(v___y_3280_, 2);
v_hasTrace_3320_ = lean_ctor_get_uint8(v_options_3319_, sizeof(void*)*1);
if (v_hasTrace_3320_ == 0)
{
lean_dec(v___x_3274_);
v___y_3296_ = v___y_3277_;
v___y_3297_ = v___y_3278_;
v___y_3298_ = v___y_3279_;
v___y_3299_ = v___y_3280_;
v___y_3300_ = v___y_3281_;
goto v___jp_3295_;
}
else
{
lean_object* v_inheritedTraceOptions_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v_inheritedTraceOptions_3321_ = lean_ctor_get(v___y_3280_, 13);
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3274_);
v___x_3323_ = l_Lean_Name_append(v___x_3322_, v___x_3274_);
v___x_3324_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3321_, v_options_3319_, v___x_3323_);
lean_dec(v___x_3323_);
if (v___x_3324_ == 0)
{
lean_dec(v___x_3274_);
v___y_3296_ = v___y_3277_;
v___y_3297_ = v___y_3278_;
v___y_3298_ = v___y_3279_;
v___y_3299_ = v___y_3280_;
v___y_3300_ = v___y_3281_;
goto v___jp_3295_;
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3325_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3264_);
v___x_3326_ = l_Nat_reprFast(v_b_3264_);
v___x_3327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
v___x_3328_ = l_Lean_MessageData_ofFormat(v___x_3327_);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3325_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
lean_inc_ref(v_xs_3275_);
v___x_3332_ = lean_array_to_list(v_xs_3275_);
v___x_3333_ = lean_box(0);
v___x_3334_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3332_, v___x_3333_);
v___x_3335_ = l_Lean_MessageData_ofList(v___x_3334_);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3331_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3274_, v___x_3336_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_dec_ref_known(v___x_3337_, 1);
v___y_3296_ = v___y_3277_;
v___y_3297_ = v___y_3278_;
v___y_3298_ = v___y_3279_;
v___y_3299_ = v___y_3280_;
v___y_3300_ = v___y_3281_;
goto v___jp_3295_;
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v_altBody_3276_);
lean_dec_ref(v_xs_3275_);
lean_dec_ref(v_e_3273_);
lean_dec_ref(v_a_3272_);
lean_dec_ref(v_containsRecFn_3268_);
lean_dec_ref(v_recFnNames_3267_);
lean_dec_ref(v_positions_3266_);
lean_dec_ref(v_recArgInfos_3265_);
lean_dec(v_b_3264_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
v___jp_3283_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = l_Lean_instInhabitedExpr;
v___x_3290_ = lean_array_get_borrowed(v___x_3289_, v_xs_3275_, v_b_3264_);
lean_dec(v_b_3264_);
lean_inc_ref(v___y_3287_);
lean_inc(v___x_3290_);
v___x_3291_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3265_, v_positions_3266_, v_recFnNames_3267_, v_containsRecFn_3268_, v___x_3290_, v_altBody_3276_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3293_ = 1;
v___x_3294_ = l_Lean_Meta_mkLambdaFVars(v_xs_3275_, v_a_3292_, v___x_3269_, v_a_3270_, v___x_3269_, v_a_3270_, v___x_3293_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec_ref(v_xs_3275_);
return v___x_3294_;
}
else
{
lean_dec_ref(v_xs_3275_);
return v___x_3291_;
}
}
v___jp_3295_:
{
lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3301_ = lean_array_get_size(v_xs_3275_);
v___x_3302_ = lean_nat_dec_eq(v___x_3301_, v___x_3271_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref(v_altBody_3276_);
lean_dec_ref(v_xs_3275_);
lean_dec_ref(v_containsRecFn_3268_);
lean_dec_ref(v_recFnNames_3267_);
lean_dec_ref(v_positions_3266_);
lean_dec_ref(v_recArgInfos_3265_);
lean_dec(v_b_3264_);
v___x_3303_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3304_ = l_Lean_indentExpr(v_a_3272_);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_indentExpr(v_e_3273_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3309_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_dec_ref(v_e_3273_);
lean_dec_ref(v_a_3272_);
v___y_3284_ = v___y_3296_;
v___y_3285_ = v___y_3297_;
v___y_3286_ = v___y_3298_;
v___y_3287_ = v___y_3299_;
v___y_3288_ = v___y_3300_;
goto v___jp_3283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v_b_3346_ = _args[0];
lean_object* v_recArgInfos_3347_ = _args[1];
lean_object* v_positions_3348_ = _args[2];
lean_object* v_recFnNames_3349_ = _args[3];
lean_object* v_containsRecFn_3350_ = _args[4];
lean_object* v___x_3351_ = _args[5];
lean_object* v_a_3352_ = _args[6];
lean_object* v___x_3353_ = _args[7];
lean_object* v_a_3354_ = _args[8];
lean_object* v_e_3355_ = _args[9];
lean_object* v___x_3356_ = _args[10];
lean_object* v_xs_3357_ = _args[11];
lean_object* v_altBody_3358_ = _args[12];
lean_object* v___y_3359_ = _args[13];
lean_object* v___y_3360_ = _args[14];
lean_object* v___y_3361_ = _args[15];
lean_object* v___y_3362_ = _args[16];
lean_object* v___y_3363_ = _args[17];
lean_object* v___y_3364_ = _args[18];
_start:
{
uint8_t v___x_33011__boxed_3365_; uint8_t v_a_33012__boxed_3366_; lean_object* v_res_3367_; 
v___x_33011__boxed_3365_ = lean_unbox(v___x_3351_);
v_a_33012__boxed_3366_ = lean_unbox(v_a_3352_);
v_res_3367_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v_b_3346_, v_recArgInfos_3347_, v_positions_3348_, v_recFnNames_3349_, v_containsRecFn_3350_, v___x_33011__boxed_3365_, v_a_33012__boxed_3366_, v___x_3353_, v_a_3354_, v_e_3355_, v___x_3356_, v_xs_3357_, v_altBody_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec(v___x_3353_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3368_, lean_object* v_positions_3369_, lean_object* v_recFnNames_3370_, lean_object* v_containsRecFn_3371_, uint8_t v_a_3372_, lean_object* v_e_3373_, lean_object* v_as_3374_, lean_object* v_bs_3375_, lean_object* v_i_3376_, lean_object* v_cs_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3384_ = lean_array_get_size(v_as_3374_);
v___x_3385_ = lean_nat_dec_lt(v_i_3376_, v___x_3384_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; 
lean_dec(v_i_3376_);
lean_dec_ref(v_e_3373_);
lean_dec_ref(v_containsRecFn_3371_);
lean_dec_ref(v_recFnNames_3370_);
lean_dec_ref(v_positions_3369_);
lean_dec_ref(v_recArgInfos_3368_);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_cs_3377_);
return v___x_3386_;
}
else
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = lean_array_get_size(v_bs_3375_);
v___x_3388_ = lean_nat_dec_lt(v_i_3376_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
lean_dec(v_i_3376_);
lean_dec_ref(v_e_3373_);
lean_dec_ref(v_containsRecFn_3371_);
lean_dec_ref(v_recFnNames_3370_);
lean_dec_ref(v_positions_3369_);
lean_dec_ref(v_recArgInfos_3368_);
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_cs_3377_);
return v___x_3389_;
}
else
{
uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v_a_3392_; lean_object* v_b_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___f_3398_; lean_object* v___x_3399_; 
v___x_3390_ = 0;
v___x_3391_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3392_ = lean_array_fget_borrowed(v_as_3374_, v_i_3376_);
v_b_3393_ = lean_array_fget_borrowed(v_bs_3375_, v_i_3376_);
v___x_3394_ = lean_unsigned_to_nat(1u);
v___x_3395_ = lean_nat_add(v_b_3393_, v___x_3394_);
v___x_3396_ = lean_box(v___x_3390_);
v___x_3397_ = lean_box(v_a_3372_);
lean_inc_ref(v_e_3373_);
lean_inc_n(v_a_3392_, 2);
lean_inc(v___x_3395_);
lean_inc_ref(v_containsRecFn_3371_);
lean_inc_ref(v_recFnNames_3370_);
lean_inc_ref(v_positions_3369_);
lean_inc_ref(v_recArgInfos_3368_);
lean_inc(v_b_3393_);
v___f_3398_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 19, 11);
lean_closure_set(v___f_3398_, 0, v_b_3393_);
lean_closure_set(v___f_3398_, 1, v_recArgInfos_3368_);
lean_closure_set(v___f_3398_, 2, v_positions_3369_);
lean_closure_set(v___f_3398_, 3, v_recFnNames_3370_);
lean_closure_set(v___f_3398_, 4, v_containsRecFn_3371_);
lean_closure_set(v___f_3398_, 5, v___x_3396_);
lean_closure_set(v___f_3398_, 6, v___x_3397_);
lean_closure_set(v___f_3398_, 7, v___x_3395_);
lean_closure_set(v___f_3398_, 8, v_a_3392_);
lean_closure_set(v___f_3398_, 9, v_e_3373_);
lean_closure_set(v___f_3398_, 10, v___x_3391_);
v___x_3399_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3392_, v___x_3395_, v___f_3398_, v___x_3390_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v___x_3401_ = lean_nat_add(v_i_3376_, v___x_3394_);
lean_dec(v_i_3376_);
v___x_3402_ = lean_array_push(v_cs_3377_, v_a_3400_);
v_i_3376_ = v___x_3401_;
v_cs_3377_ = v___x_3402_;
goto _start;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v_cs_3377_);
lean_dec(v_i_3376_);
lean_dec_ref(v_e_3373_);
lean_dec_ref(v_containsRecFn_3371_);
lean_dec_ref(v_recFnNames_3370_);
lean_dec_ref(v_positions_3369_);
lean_dec_ref(v_recArgInfos_3368_);
v_a_3404_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3399_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3399_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
return v___x_3414_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
return v___x_3417_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3420_ = l_Lean_stringToMessageData(v___x_3419_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3421_, lean_object* v_positions_3422_, lean_object* v_recFnNames_3423_, lean_object* v_containsRecFn_3424_, lean_object* v_below_3425_, lean_object* v_e_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v_e_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___x_3446_; 
lean_inc_ref(v_containsRecFn_3424_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3427_);
lean_inc_ref(v_e_3426_);
v___x_3446_ = lean_apply_7(v_containsRecFn_3424_, v_e_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, lean_box(0));
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3669_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3669_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3669_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_unbox(v_a_3447_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3453_; 
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v_e_3426_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_e_3426_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
else
{
uint8_t v___x_3455_; 
lean_del_object(v___x_3449_);
v___x_3455_ = 0;
switch(lean_obj_tag(v_e_3426_))
{
case 6:
{
lean_object* v_binderName_3456_; lean_object* v_binderType_3457_; lean_object* v_body_3458_; uint8_t v_binderInfo_3459_; lean_object* v___x_3460_; 
v_binderName_3456_ = lean_ctor_get(v_e_3426_, 0);
lean_inc(v_binderName_3456_);
v_binderType_3457_ = lean_ctor_get(v_e_3426_, 1);
lean_inc_ref(v_binderType_3457_);
v_body_3458_ = lean_ctor_get(v_e_3426_, 2);
lean_inc_ref(v_body_3458_);
v_binderInfo_3459_ = lean_ctor_get_uint8(v_e_3426_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3426_, 3);
lean_inc_ref(v_a_3430_);
lean_inc_ref(v_below_3425_);
lean_inc_ref(v_containsRecFn_3424_);
lean_inc_ref(v_recFnNames_3423_);
lean_inc_ref(v_positions_3422_);
lean_inc_ref(v_recArgInfos_3421_);
v___x_3460_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v_below_3425_, v_binderType_3457_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; lean_object* v___f_3463_; uint8_t v___x_3464_; lean_object* v___x_3465_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v___x_3462_ = lean_box(v___x_3455_);
v___f_3463_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3463_, 0, v_body_3458_);
lean_closure_set(v___f_3463_, 1, v_recArgInfos_3421_);
lean_closure_set(v___f_3463_, 2, v_positions_3422_);
lean_closure_set(v___f_3463_, 3, v_recFnNames_3423_);
lean_closure_set(v___f_3463_, 4, v_containsRecFn_3424_);
lean_closure_set(v___f_3463_, 5, v_below_3425_);
lean_closure_set(v___f_3463_, 6, v___x_3462_);
lean_closure_set(v___f_3463_, 7, v_a_3447_);
v___x_3464_ = 0;
v___x_3465_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3456_, v_binderInfo_3459_, v_a_3461_, v___f_3463_, v___x_3464_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec_ref(v_a_3430_);
return v___x_3465_;
}
else
{
lean_dec_ref(v_body_3458_);
lean_dec(v_binderName_3456_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
return v___x_3460_;
}
}
case 7:
{
lean_object* v_binderName_3466_; lean_object* v_binderType_3467_; lean_object* v_body_3468_; uint8_t v_binderInfo_3469_; lean_object* v___x_3470_; 
v_binderName_3466_ = lean_ctor_get(v_e_3426_, 0);
lean_inc(v_binderName_3466_);
v_binderType_3467_ = lean_ctor_get(v_e_3426_, 1);
lean_inc_ref(v_binderType_3467_);
v_body_3468_ = lean_ctor_get(v_e_3426_, 2);
lean_inc_ref(v_body_3468_);
v_binderInfo_3469_ = lean_ctor_get_uint8(v_e_3426_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3426_, 3);
lean_inc_ref(v_a_3430_);
lean_inc_ref(v_below_3425_);
lean_inc_ref(v_containsRecFn_3424_);
lean_inc_ref(v_recFnNames_3423_);
lean_inc_ref(v_positions_3422_);
lean_inc_ref(v_recArgInfos_3421_);
v___x_3470_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v_below_3425_, v_binderType_3467_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3472_; lean_object* v___f_3473_; uint8_t v___x_3474_; lean_object* v___x_3475_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v___x_3472_ = lean_box(v___x_3455_);
v___f_3473_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3473_, 0, v_body_3468_);
lean_closure_set(v___f_3473_, 1, v_recArgInfos_3421_);
lean_closure_set(v___f_3473_, 2, v_positions_3422_);
lean_closure_set(v___f_3473_, 3, v_recFnNames_3423_);
lean_closure_set(v___f_3473_, 4, v_containsRecFn_3424_);
lean_closure_set(v___f_3473_, 5, v_below_3425_);
lean_closure_set(v___f_3473_, 6, v___x_3472_);
lean_closure_set(v___f_3473_, 7, v_a_3447_);
v___x_3474_ = 0;
v___x_3475_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3466_, v_binderInfo_3469_, v_a_3471_, v___f_3473_, v___x_3474_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec_ref(v_a_3430_);
return v___x_3475_;
}
else
{
lean_dec_ref(v_body_3468_);
lean_dec(v_binderName_3466_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
return v___x_3470_;
}
}
case 8:
{
lean_object* v_declName_3476_; lean_object* v_type_3477_; lean_object* v_value_3478_; lean_object* v_body_3479_; uint8_t v_nondep_3480_; lean_object* v___x_3481_; 
lean_dec(v_a_3447_);
v_declName_3476_ = lean_ctor_get(v_e_3426_, 0);
lean_inc(v_declName_3476_);
v_type_3477_ = lean_ctor_get(v_e_3426_, 1);
lean_inc_ref(v_type_3477_);
v_value_3478_ = lean_ctor_get(v_e_3426_, 2);
lean_inc_ref(v_value_3478_);
v_body_3479_ = lean_ctor_get(v_e_3426_, 3);
lean_inc_ref(v_body_3479_);
v_nondep_3480_ = lean_ctor_get_uint8(v_e_3426_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3426_, 4);
lean_inc_ref(v_a_3430_);
lean_inc_ref(v_below_3425_);
lean_inc_ref(v_containsRecFn_3424_);
lean_inc_ref(v_recFnNames_3423_);
lean_inc_ref(v_positions_3422_);
lean_inc_ref(v_recArgInfos_3421_);
v___x_3481_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v_below_3425_, v_type_3477_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
lean_inc_ref(v_a_3430_);
lean_inc_ref(v_below_3425_);
lean_inc_ref(v_containsRecFn_3424_);
lean_inc_ref(v_recFnNames_3423_);
lean_inc_ref(v_positions_3422_);
lean_inc_ref(v_recArgInfos_3421_);
v___x_3483_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v_below_3425_, v_value_3478_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___f_3485_; uint8_t v___x_3486_; lean_object* v___x_3487_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___f_3485_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3485_, 0, v_body_3479_);
lean_closure_set(v___f_3485_, 1, v_recArgInfos_3421_);
lean_closure_set(v___f_3485_, 2, v_positions_3422_);
lean_closure_set(v___f_3485_, 3, v_recFnNames_3423_);
lean_closure_set(v___f_3485_, 4, v_containsRecFn_3424_);
lean_closure_set(v___f_3485_, 5, v_below_3425_);
v___x_3486_ = 0;
v___x_3487_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3476_, v_a_3482_, v_a_3484_, v___f_3485_, v_nondep_3480_, v___x_3486_, v___x_3455_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec_ref(v_a_3430_);
return v___x_3487_;
}
else
{
lean_dec(v_a_3482_);
lean_dec_ref(v_body_3479_);
lean_dec(v_declName_3476_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
return v___x_3483_;
}
}
else
{
lean_dec_ref(v_body_3479_);
lean_dec_ref(v_value_3478_);
lean_dec(v_declName_3476_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
return v___x_3481_;
}
}
case 10:
{
lean_object* v_data_3488_; lean_object* v_expr_3489_; lean_object* v___x_3490_; 
lean_dec(v_a_3447_);
v_data_3488_ = lean_ctor_get(v_e_3426_, 0);
lean_inc(v_data_3488_);
v_expr_3489_ = lean_ctor_get(v_e_3426_, 1);
lean_inc_ref(v_expr_3489_);
v___x_3490_ = l_Lean_getRecAppSyntax_x3f(v_e_3426_);
lean_dec_ref_known(v_e_3426_, 2);
if (lean_obj_tag(v___x_3490_) == 1)
{
lean_object* v_val_3491_; lean_object* v_fileName_3492_; lean_object* v_fileMap_3493_; lean_object* v_options_3494_; lean_object* v_currRecDepth_3495_; lean_object* v_maxRecDepth_3496_; lean_object* v_ref_3497_; lean_object* v_currNamespace_3498_; lean_object* v_openDecls_3499_; lean_object* v_initHeartbeats_3500_; lean_object* v_maxHeartbeats_3501_; lean_object* v_quotContext_3502_; lean_object* v_currMacroScope_3503_; uint8_t v_diag_3504_; lean_object* v_cancelTk_x3f_3505_; uint8_t v_suppressElabErrors_3506_; lean_object* v_inheritedTraceOptions_3507_; lean_object* v_ref_3508_; lean_object* v___x_3509_; 
lean_dec(v_data_3488_);
v_val_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_val_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v_fileName_3492_ = lean_ctor_get(v_a_3430_, 0);
lean_inc_ref(v_fileName_3492_);
v_fileMap_3493_ = lean_ctor_get(v_a_3430_, 1);
lean_inc_ref(v_fileMap_3493_);
v_options_3494_ = lean_ctor_get(v_a_3430_, 2);
lean_inc_ref(v_options_3494_);
v_currRecDepth_3495_ = lean_ctor_get(v_a_3430_, 3);
lean_inc(v_currRecDepth_3495_);
v_maxRecDepth_3496_ = lean_ctor_get(v_a_3430_, 4);
lean_inc(v_maxRecDepth_3496_);
v_ref_3497_ = lean_ctor_get(v_a_3430_, 5);
lean_inc(v_ref_3497_);
v_currNamespace_3498_ = lean_ctor_get(v_a_3430_, 6);
lean_inc(v_currNamespace_3498_);
v_openDecls_3499_ = lean_ctor_get(v_a_3430_, 7);
lean_inc(v_openDecls_3499_);
v_initHeartbeats_3500_ = lean_ctor_get(v_a_3430_, 8);
lean_inc(v_initHeartbeats_3500_);
v_maxHeartbeats_3501_ = lean_ctor_get(v_a_3430_, 9);
lean_inc(v_maxHeartbeats_3501_);
v_quotContext_3502_ = lean_ctor_get(v_a_3430_, 10);
lean_inc(v_quotContext_3502_);
v_currMacroScope_3503_ = lean_ctor_get(v_a_3430_, 11);
lean_inc(v_currMacroScope_3503_);
v_diag_3504_ = lean_ctor_get_uint8(v_a_3430_, sizeof(void*)*14);
v_cancelTk_x3f_3505_ = lean_ctor_get(v_a_3430_, 12);
lean_inc(v_cancelTk_x3f_3505_);
v_suppressElabErrors_3506_ = lean_ctor_get_uint8(v_a_3430_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3507_ = lean_ctor_get(v_a_3430_, 13);
lean_inc_ref(v_inheritedTraceOptions_3507_);
lean_dec_ref(v_a_3430_);
v_ref_3508_ = l_Lean_replaceRef(v_val_3491_, v_ref_3497_);
lean_dec(v_ref_3497_);
lean_dec(v_val_3491_);
v___x_3509_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3509_, 0, v_fileName_3492_);
lean_ctor_set(v___x_3509_, 1, v_fileMap_3493_);
lean_ctor_set(v___x_3509_, 2, v_options_3494_);
lean_ctor_set(v___x_3509_, 3, v_currRecDepth_3495_);
lean_ctor_set(v___x_3509_, 4, v_maxRecDepth_3496_);
lean_ctor_set(v___x_3509_, 5, v_ref_3508_);
lean_ctor_set(v___x_3509_, 6, v_currNamespace_3498_);
lean_ctor_set(v___x_3509_, 7, v_openDecls_3499_);
lean_ctor_set(v___x_3509_, 8, v_initHeartbeats_3500_);
lean_ctor_set(v___x_3509_, 9, v_maxHeartbeats_3501_);
lean_ctor_set(v___x_3509_, 10, v_quotContext_3502_);
lean_ctor_set(v___x_3509_, 11, v_currMacroScope_3503_);
lean_ctor_set(v___x_3509_, 12, v_cancelTk_x3f_3505_);
lean_ctor_set(v___x_3509_, 13, v_inheritedTraceOptions_3507_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*14, v_diag_3504_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*14 + 1, v_suppressElabErrors_3506_);
v_e_3426_ = v_expr_3489_;
v_a_3430_ = v___x_3509_;
goto _start;
}
else
{
lean_object* v___x_3511_; 
lean_dec(v___x_3490_);
v___x_3511_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v_below_3425_, v_expr_3489_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3520_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3516_ = l_Lean_mkMData(v_data_3488_, v_a_3512_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3516_);
v___x_3518_ = v___x_3514_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
else
{
lean_dec(v_data_3488_);
return v___x_3511_;
}
}
}
case 11:
{
lean_object* v_typeName_3521_; lean_object* v_idx_3522_; lean_object* v_struct_3523_; lean_object* v___x_3524_; 
lean_dec(v_a_3447_);
v_typeName_3521_ = lean_ctor_get(v_e_3426_, 0);
lean_inc(v_typeName_3521_);
v_idx_3522_ = lean_ctor_get(v_e_3426_, 1);
lean_inc(v_idx_3522_);
v_struct_3523_ = lean_ctor_get(v_e_3426_, 2);
lean_inc_ref(v_struct_3523_);
lean_dec_ref_known(v_e_3426_, 3);
v___x_3524_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v_below_3425_, v_struct_3523_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3533_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3533_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3533_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = l_Lean_mkProj(v_typeName_3521_, v_idx_3522_, v_a_3525_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3529_);
v___x_3531_ = v___x_3527_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
else
{
lean_dec(v_idx_3522_);
lean_dec(v_typeName_3521_);
return v___x_3524_;
}
}
case 5:
{
uint8_t v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = lean_unbox(v_a_3447_);
lean_inc_ref(v_e_3426_);
v___x_3535_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3426_, v___x_3534_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
if (lean_obj_tag(v_a_3536_) == 0)
{
lean_dec(v_a_3447_);
v_e_3434_ = v_e_3426_;
v___y_3435_ = v_a_3427_;
v___y_3436_ = v_a_3428_;
v___y_3437_ = v_a_3429_;
v___y_3438_ = v_a_3430_;
v___y_3439_ = v_a_3431_;
goto v___jp_3433_;
}
else
{
lean_object* v_val_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v_val_3537_ = lean_ctor_get(v_a_3536_, 0);
lean_inc(v_val_3537_);
lean_dec_ref_known(v_a_3536_, 1);
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3539_ = lean_array_get_size(v_recArgInfos_3421_);
v___x_3540_ = lean_nat_dec_lt(v___x_3538_, v___x_3539_);
if (v___x_3540_ == 0)
{
lean_dec(v_val_3537_);
lean_dec(v_a_3447_);
v_e_3434_ = v_e_3426_;
v___y_3435_ = v_a_3427_;
v___y_3436_ = v_a_3428_;
v___y_3437_ = v_a_3429_;
v___y_3438_ = v_a_3430_;
v___y_3439_ = v_a_3431_;
goto v___jp_3433_;
}
else
{
if (v___x_3540_ == 0)
{
lean_dec(v_val_3537_);
lean_dec(v_a_3447_);
v_e_3434_ = v_e_3426_;
v___y_3435_ = v_a_3427_;
v___y_3436_ = v_a_3428_;
v___y_3437_ = v_a_3429_;
v___y_3438_ = v_a_3430_;
v___y_3439_ = v_a_3431_;
goto v___jp_3433_;
}
else
{
size_t v___x_3541_; size_t v___x_3542_; uint8_t v___x_3543_; 
v___x_3541_ = ((size_t)0ULL);
v___x_3542_ = lean_usize_of_nat(v___x_3539_);
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3426_, v_recArgInfos_3421_, v___x_3541_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_dec(v_val_3537_);
lean_dec(v_a_3447_);
v_e_3434_ = v_e_3426_;
v___y_3435_ = v_a_3427_;
v___y_3436_ = v_a_3428_;
v___y_3437_ = v_a_3429_;
v___y_3438_ = v_a_3430_;
v___y_3439_ = v_a_3431_;
goto v___jp_3433_;
}
else
{
lean_object* v_inheritedTraceOptions_3544_; lean_object* v___x_3545_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___x_3615_; 
v_inheritedTraceOptions_3544_ = lean_ctor_get(v_a_3430_, 13);
v___x_3545_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3615_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3545_, v_inheritedTraceOptions_3544_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; uint8_t v___x_3617_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v___x_3617_ = lean_unbox(v_a_3616_);
lean_dec(v_a_3616_);
if (v___x_3617_ == 0)
{
v___y_3547_ = v_a_3427_;
v___y_3548_ = v_a_3428_;
v___y_3549_ = v_a_3429_;
v___y_3550_ = v_a_3430_;
v___y_3551_ = v_a_3431_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3618_; 
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc_ref(v_below_3425_);
v___x_3618_ = lean_infer_type(v_below_3425_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3620_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3425_);
v___x_3621_ = l_Lean_MessageData_ofExpr(v_below_3425_);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Lean_MessageData_ofExpr(v_a_3619_);
v___x_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3545_, v___x_3626_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_dec_ref_known(v___x_3627_, 1);
v___y_3547_ = v_a_3427_;
v___y_3548_ = v_a_3428_;
v___y_3549_ = v_a_3429_;
v___y_3550_ = v_a_3430_;
v___y_3551_ = v_a_3431_;
goto v___jp_3546_;
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v_val_3537_);
lean_dec_ref_known(v_e_3426_, 2);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
else
{
lean_dec(v_val_3537_);
lean_dec_ref_known(v_e_3426_, 2);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
return v___x_3618_;
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec(v_val_3537_);
lean_dec_ref_known(v_e_3426_, 2);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v_a_3636_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3615_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3615_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
v___jp_3546_:
{
lean_object* v___x_3552_; 
lean_inc_ref(v_below_3425_);
v___x_3552_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3537_, v_below_3425_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
if (lean_obj_tag(v_a_3553_) == 1)
{
lean_object* v_val_3554_; lean_object* v_toMatcherInfo_3555_; lean_object* v_matcherName_3556_; lean_object* v_matcherLevels_3557_; lean_object* v_params_3558_; lean_object* v_motive_3559_; lean_object* v_discrs_3560_; lean_object* v_alts_3561_; lean_object* v_remaining_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; lean_object* v___x_3566_; 
lean_dec_ref(v_below_3425_);
v_val_3554_ = lean_ctor_get(v_a_3553_, 0);
lean_inc(v_val_3554_);
lean_dec_ref_known(v_a_3553_, 1);
v_toMatcherInfo_3555_ = lean_ctor_get(v_val_3554_, 0);
lean_inc_ref(v_toMatcherInfo_3555_);
v_matcherName_3556_ = lean_ctor_get(v_val_3554_, 1);
lean_inc(v_matcherName_3556_);
v_matcherLevels_3557_ = lean_ctor_get(v_val_3554_, 2);
lean_inc_ref(v_matcherLevels_3557_);
v_params_3558_ = lean_ctor_get(v_val_3554_, 3);
lean_inc_ref(v_params_3558_);
v_motive_3559_ = lean_ctor_get(v_val_3554_, 4);
lean_inc_ref(v_motive_3559_);
v_discrs_3560_ = lean_ctor_get(v_val_3554_, 5);
lean_inc_ref(v_discrs_3560_);
v_alts_3561_ = lean_ctor_get(v_val_3554_, 6);
lean_inc_ref(v_alts_3561_);
v_remaining_3562_ = lean_ctor_get(v_val_3554_, 7);
lean_inc_ref(v_remaining_3562_);
v___x_3563_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3554_);
v___x_3564_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3565_ = lean_unbox(v_a_3447_);
lean_dec(v_a_3447_);
v___x_3566_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v___x_3565_, v_e_3426_, v_alts_3561_, v___x_3563_, v___x_3538_, v___x_3564_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___x_3563_);
lean_dec_ref(v_alts_3561_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3576_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3576_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3576_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3571_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3571_, 0, v_toMatcherInfo_3555_);
lean_ctor_set(v___x_3571_, 1, v_matcherName_3556_);
lean_ctor_set(v___x_3571_, 2, v_matcherLevels_3557_);
lean_ctor_set(v___x_3571_, 3, v_params_3558_);
lean_ctor_set(v___x_3571_, 4, v_motive_3559_);
lean_ctor_set(v___x_3571_, 5, v_discrs_3560_);
lean_ctor_set(v___x_3571_, 6, v_a_3567_);
lean_ctor_set(v___x_3571_, 7, v_remaining_3562_);
v___x_3572_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3571_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3572_);
v___x_3574_ = v___x_3569_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v_remaining_3562_);
lean_dec_ref(v_discrs_3560_);
lean_dec_ref(v_motive_3559_);
lean_dec_ref(v_params_3558_);
lean_dec_ref(v_matcherLevels_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
v_a_3577_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3566_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3566_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3585_; lean_object* v___x_3586_; 
lean_dec(v_a_3553_);
lean_dec(v_a_3447_);
v_inheritedTraceOptions_3585_ = lean_ctor_get(v___y_3550_, 13);
v___x_3586_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3545_, v_inheritedTraceOptions_3585_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; uint8_t v___x_3588_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref_known(v___x_3586_, 1);
v___x_3588_ = lean_unbox(v_a_3587_);
lean_dec(v_a_3587_);
if (v___x_3588_ == 0)
{
v_e_3434_ = v_e_3426_;
v___y_3435_ = v___y_3547_;
v___y_3436_ = v___y_3548_;
v___y_3437_ = v___y_3549_;
v___y_3438_ = v___y_3550_;
v___y_3439_ = v___y_3551_;
goto v___jp_3433_;
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3590_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3545_, v___x_3589_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_dec_ref_known(v___x_3590_, 1);
v_e_3434_ = v_e_3426_;
v___y_3435_ = v___y_3547_;
v___y_3436_ = v___y_3548_;
v___y_3437_ = v___y_3549_;
v___y_3438_ = v___y_3550_;
v___y_3439_ = v___y_3551_;
goto v___jp_3433_;
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref(v___y_3550_);
lean_dec_ref_known(v_e_3426_, 2);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref(v___y_3550_);
lean_dec_ref_known(v_e_3426_, 2);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v_a_3599_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3586_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3586_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v___y_3550_);
lean_dec_ref_known(v_e_3426_, 2);
lean_dec(v_a_3447_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v_a_3607_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3552_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3552_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec_ref_known(v_e_3426_, 2);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v_a_3644_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3535_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3535_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
default: 
{
lean_object* v___x_3652_; 
lean_dec(v_a_3447_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
lean_inc_ref(v_e_3426_);
v___x_3652_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3423_, v_e_3426_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec_ref(v_a_3430_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v___x_3652_, 0);
lean_dec(v_unused_3660_);
v___x_3654_ = v___x_3652_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_dec(v___x_3652_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v_e_3426_);
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_e_3426_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec_ref(v_e_3426_);
v_a_3661_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3652_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3652_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_e_3426_);
lean_dec_ref(v_below_3425_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v_a_3670_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3446_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3446_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
v___jp_3433_:
{
lean_object* v_dummy_3440_; lean_object* v_nargs_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_dummy_3440_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3441_ = l_Lean_Expr_getAppNumArgs(v_e_3434_);
lean_inc(v_nargs_3441_);
v___x_3442_ = lean_mk_array(v_nargs_3441_, v_dummy_3440_);
v___x_3443_ = lean_unsigned_to_nat(1u);
v___x_3444_ = lean_nat_sub(v_nargs_3441_, v___x_3443_);
lean_dec(v_nargs_3441_);
lean_inc_ref(v_e_3434_);
v___x_3445_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v_below_3425_, v_e_3434_, v_e_3434_, v___x_3442_, v___x_3444_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec_ref(v___y_3438_);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3678_, lean_object* v_recArgInfos_3679_, lean_object* v_positions_3680_, lean_object* v_recFnNames_3681_, lean_object* v_containsRecFn_3682_, lean_object* v_below_3683_, lean_object* v_x_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_expr_instantiate1(v_body_3678_, v_x_3684_);
lean_inc_ref(v___y_3688_);
v___x_3692_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3679_, v_positions_3680_, v_recFnNames_3681_, v_containsRecFn_3682_, v_below_3683_, v___x_3691_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3693_, lean_object* v_positions_3694_, lean_object* v_recFnNames_3695_, lean_object* v_containsRecFn_3696_, lean_object* v_below_3697_, lean_object* v_sz_3698_, lean_object* v_i_3699_, lean_object* v_bs_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
size_t v_sz_boxed_3707_; size_t v_i_boxed_3708_; lean_object* v_res_3709_; 
v_sz_boxed_3707_ = lean_unbox_usize(v_sz_3698_);
lean_dec(v_sz_3698_);
v_i_boxed_3708_ = lean_unbox_usize(v_i_3699_);
lean_dec(v_i_3699_);
v_res_3709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3693_, v_positions_3694_, v_recFnNames_3695_, v_containsRecFn_3696_, v_below_3697_, v_sz_boxed_3707_, v_i_boxed_3708_, v_bs_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3710_, lean_object* v_positions_3711_, lean_object* v_recFnNames_3712_, lean_object* v_containsRecFn_3713_, lean_object* v_a_3714_, lean_object* v_e_3715_, lean_object* v_as_3716_, lean_object* v_bs_3717_, lean_object* v_i_3718_, lean_object* v_cs_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
uint8_t v_a_32971__boxed_3726_; lean_object* v_res_3727_; 
v_a_32971__boxed_3726_ = lean_unbox(v_a_3714_);
v_res_3727_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3710_, v_positions_3711_, v_recFnNames_3712_, v_containsRecFn_3713_, v_a_32971__boxed_3726_, v_e_3715_, v_as_3716_, v_bs_3717_, v_i_3718_, v_cs_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v_bs_3717_);
lean_dec_ref(v_as_3716_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3728_, lean_object* v_positions_3729_, lean_object* v_recFnNames_3730_, lean_object* v_containsRecFn_3731_, lean_object* v_below_3732_, lean_object* v_e_3733_, lean_object* v_x_3734_, lean_object* v_x_3735_, lean_object* v_x_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3728_, v_positions_3729_, v_recFnNames_3730_, v_containsRecFn_3731_, v_below_3732_, v_e_3733_, v_x_3734_, v_x_3735_, v_x_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3744_, lean_object* v_positions_3745_, lean_object* v_recFnNames_3746_, lean_object* v_containsRecFn_3747_, lean_object* v_below_3748_, lean_object* v_e_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3744_, v_positions_3745_, v_recFnNames_3746_, v_containsRecFn_3747_, v_below_3748_, v_e_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
lean_dec(v_a_3754_);
lean_dec(v_a_3752_);
lean_dec_ref(v_a_3751_);
lean_dec(v_a_3750_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3757_, lean_object* v_msg_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3758_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3766_, lean_object* v_msg_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3766_, v_msg_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3775_, lean_object* v_name_3776_, lean_object* v_type_3777_, lean_object* v_val_3778_, lean_object* v_k_3779_, uint8_t v_nondep_3780_, uint8_t v_kind_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3776_, v_type_3777_, v_val_3778_, v_k_3779_, v_nondep_3780_, v_kind_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3789_, lean_object* v_name_3790_, lean_object* v_type_3791_, lean_object* v_val_3792_, lean_object* v_k_3793_, lean_object* v_nondep_3794_, lean_object* v_kind_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
uint8_t v_nondep_boxed_3802_; uint8_t v_kind_boxed_3803_; lean_object* v_res_3804_; 
v_nondep_boxed_3802_ = lean_unbox(v_nondep_3794_);
v_kind_boxed_3803_ = lean_unbox(v_kind_3795_);
v_res_3804_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3789_, v_name_3790_, v_type_3791_, v_val_3792_, v_k_3793_, v_nondep_boxed_3802_, v_kind_boxed_3803_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3805_, v___y_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3821_, lean_object* v_msg_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3821_, v_msg_3822_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3830_, lean_object* v_msg_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3830_, v_msg_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3839_, lean_object* v_constName_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3848_, lean_object* v_constName_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3848_, v_constName_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3857_, lean_object* v_ref_3858_, lean_object* v_constName_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3858_, v_constName_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3867_, lean_object* v_ref_3868_, lean_object* v_constName_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3867_, v_ref_3868_, v_constName_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec(v_ref_3868_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3877_, lean_object* v_ref_3878_, lean_object* v_msg_3879_, lean_object* v_declHint_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3878_, v_msg_3879_, v_declHint_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3888_, lean_object* v_ref_3889_, lean_object* v_msg_3890_, lean_object* v_declHint_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3888_, v_ref_3889_, v_msg_3890_, v_declHint_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec(v_ref_3889_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3899_, lean_object* v_declHint_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3899_, v_declHint_3900_, v___y_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3908_, lean_object* v_declHint_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3908_, v_declHint_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3917_, lean_object* v_ref_3918_, lean_object* v_msg_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3918_, v_msg_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3927_, lean_object* v_ref_3928_, lean_object* v_msg_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3927_, v_ref_3928_, v_msg_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec(v_ref_3928_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3937_, lean_object* v_e_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v_fst_3947_; lean_object* v_snd_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3945_ = lean_st_ref_take(v___y_3939_);
v___x_3946_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3937_, v_e_3938_, v___x_3945_);
v_fst_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_fst_3947_);
v_snd_3948_ = lean_ctor_get(v___x_3946_, 1);
lean_inc(v_snd_3948_);
lean_dec_ref(v___x_3946_);
v___x_3949_ = lean_st_ref_put(v___y_3939_, v_snd_3948_);
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v_fst_3947_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3951_, lean_object* v_e_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3951_, v_e_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v_recFnNames_3951_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3960_, size_t v_i_3961_, lean_object* v_bs_3962_){
_start:
{
uint8_t v___x_3963_; 
v___x_3963_ = lean_usize_dec_lt(v_i_3961_, v_sz_3960_);
if (v___x_3963_ == 0)
{
return v_bs_3962_;
}
else
{
lean_object* v_v_3964_; lean_object* v_fnName_3965_; lean_object* v___x_3966_; lean_object* v_bs_x27_3967_; size_t v___x_3968_; size_t v___x_3969_; lean_object* v___x_3970_; 
v_v_3964_ = lean_array_uget_borrowed(v_bs_3962_, v_i_3961_);
v_fnName_3965_ = lean_ctor_get(v_v_3964_, 0);
lean_inc(v_fnName_3965_);
v___x_3966_ = lean_unsigned_to_nat(0u);
v_bs_x27_3967_ = lean_array_uset(v_bs_3962_, v_i_3961_, v___x_3966_);
v___x_3968_ = ((size_t)1ULL);
v___x_3969_ = lean_usize_add(v_i_3961_, v___x_3968_);
v___x_3970_ = lean_array_uset(v_bs_x27_3967_, v_i_3961_, v_fnName_3965_);
v_i_3961_ = v___x_3969_;
v_bs_3962_ = v___x_3970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3972_, lean_object* v_i_3973_, lean_object* v_bs_3974_){
_start:
{
size_t v_sz_boxed_3975_; size_t v_i_boxed_3976_; lean_object* v_res_3977_; 
v_sz_boxed_3975_ = lean_unbox_usize(v_sz_3972_);
lean_dec(v_sz_3972_);
v_i_boxed_3976_ = lean_unbox_usize(v_i_3973_);
lean_dec(v_i_3973_);
v_res_3977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3975_, v_i_boxed_3976_, v_bs_3974_);
return v_res_3977_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v_cellCount_3978_; lean_object* v___x_3979_; 
v_cellCount_3978_ = lean_unsigned_to_nat(16u);
v___x_3979_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3978_);
return v___x_3979_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v_cellCount_3980_; lean_object* v___x_3981_; 
v_cellCount_3980_ = lean_unsigned_to_nat(16u);
v___x_3981_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3980_);
return v___x_3981_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__2(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3982_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3983_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3984_ = lean_unsigned_to_nat(0u);
v___x_3985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
lean_ctor_set(v___x_3985_, 1, v___x_3983_);
lean_ctor_set(v___x_3985_, 2, v___x_3982_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3986_, lean_object* v_positions_3987_, lean_object* v_below_3988_, lean_object* v_e_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; size_t v_sz_3997_; size_t v___x_3998_; lean_object* v_recFnNames_3999_; lean_object* v_containsRecFn_4000_; lean_object* v___x_4001_; 
v___x_3995_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__2);
v___x_3996_ = lean_st_mk_ref(v___x_3995_);
v_sz_3997_ = lean_array_size(v_recArgInfos_3986_);
v___x_3998_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3986_);
v_recFnNames_3999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3997_, v___x_3998_, v_recArgInfos_3986_);
lean_inc_ref(v_recFnNames_3999_);
v_containsRecFn_4000_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_4000_, 0, v_recFnNames_3999_);
lean_inc_ref(v_a_3992_);
v___x_4001_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3986_, v_positions_3987_, v_recFnNames_3999_, v_containsRecFn_4000_, v_below_3988_, v_e_3989_, v___x_3996_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4010_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4004_ = v___x_4001_;
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_4001_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4008_; 
v___x_4006_ = lean_st_ref_get(v___x_3996_);
lean_dec(v___x_3996_);
lean_dec(v___x_4006_);
if (v_isShared_4005_ == 0)
{
v___x_4008_ = v___x_4004_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4002_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
else
{
lean_dec(v___x_3996_);
return v___x_4001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_4011_, lean_object* v_positions_4012_, lean_object* v_below_4013_, lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4011_, v_positions_4012_, v_below_4013_, v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_4021_, lean_object* v_k_4022_, uint8_t v_cleanupAnnotations_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___f_4029_; uint8_t v___x_4030_; uint8_t v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___f_4029_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4029_, 0, v_k_4022_);
v___x_4030_ = 1;
v___x_4031_ = 0;
v___x_4032_ = lean_box(0);
v___x_4033_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4021_, v___x_4030_, v___x_4031_, v___x_4030_, v___x_4031_, v___x_4032_, v___f_4029_, v_cleanupAnnotations_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4033_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4033_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4050_, lean_object* v_k_4051_, lean_object* v_cleanupAnnotations_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4058_; lean_object* v_res_4059_; 
v_cleanupAnnotations_boxed_4058_ = lean_unbox(v_cleanupAnnotations_4052_);
v_res_4059_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4050_, v_k_4051_, v_cleanupAnnotations_boxed_4058_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4060_, lean_object* v_e_4061_, lean_object* v_k_4062_, uint8_t v_cleanupAnnotations_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4061_, v_k_4062_, v_cleanupAnnotations_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4070_, lean_object* v_e_4071_, lean_object* v_k_4072_, lean_object* v_cleanupAnnotations_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4079_; lean_object* v_res_4080_; 
v_cleanupAnnotations_boxed_4079_ = lean_unbox(v_cleanupAnnotations_4073_);
v_res_4080_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4070_, v_e_4071_, v_k_4072_, v_cleanupAnnotations_boxed_4079_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4081_, lean_object* v_recArgInfo_4082_, lean_object* v_xs_4083_, lean_object* v___value_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lean_Meta_instantiateForall(v_type_4081_, v_xs_4083_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4092_; lean_object* v_fst_4093_; lean_object* v_snd_4094_; uint8_t v___x_4095_; uint8_t v___x_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v___x_4090_, 1);
v___x_4092_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4082_, v_xs_4083_);
v_fst_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_fst_4093_);
v_snd_4094_ = lean_ctor_get(v___x_4092_, 1);
lean_inc(v_snd_4094_);
lean_dec_ref(v___x_4092_);
v___x_4095_ = 0;
v___x_4096_ = 1;
v___x_4097_ = 1;
v___x_4098_ = l_Lean_Meta_mkForallFVars(v_snd_4094_, v_a_4091_, v___x_4095_, v___x_4096_, v___x_4096_, v___x_4097_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v_snd_4094_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4100_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
v___x_4100_ = l_Lean_Meta_mkLambdaFVars(v_fst_4093_, v_a_4099_, v___x_4095_, v___x_4096_, v___x_4095_, v___x_4096_, v___x_4097_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v_fst_4093_);
return v___x_4100_;
}
else
{
lean_dec(v_fst_4093_);
return v___x_4098_;
}
}
else
{
lean_dec_ref(v_xs_4083_);
lean_dec_ref(v_recArgInfo_4082_);
return v___x_4090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4101_, lean_object* v_recArgInfo_4102_, lean_object* v_xs_4103_, lean_object* v___value_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4101_, v_recArgInfo_4102_, v_xs_4103_, v___value_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec_ref(v___value_4104_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4111_, lean_object* v_value_4112_, lean_object* v_type_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v___f_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; 
v___f_4119_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4119_, 0, v_type_4113_);
lean_closure_set(v___f_4119_, 1, v_recArgInfo_4111_);
v___x_4120_ = 0;
v___x_4121_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4112_, v___f_4119_, v___x_4120_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4122_, lean_object* v_value_4123_, lean_object* v_type_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4122_, v_value_4123_, v_type_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4131_, lean_object* v_maxFVars_x3f_4132_, lean_object* v_k_4133_, uint8_t v_cleanupAnnotations_4134_, uint8_t v_whnfType_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___f_4141_; lean_object* v___x_4142_; 
v___f_4141_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4141_, 0, v_k_4133_);
v___x_4142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4131_, v_maxFVars_x3f_4132_, v___f_4141_, v_cleanupAnnotations_4134_, v_whnfType_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4142_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4142_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
v_a_4151_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4142_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4142_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4159_, lean_object* v_maxFVars_x3f_4160_, lean_object* v_k_4161_, lean_object* v_cleanupAnnotations_4162_, lean_object* v_whnfType_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4169_; uint8_t v_whnfType_boxed_4170_; lean_object* v_res_4171_; 
v_cleanupAnnotations_boxed_4169_ = lean_unbox(v_cleanupAnnotations_4162_);
v_whnfType_boxed_4170_ = lean_unbox(v_whnfType_4163_);
v_res_4171_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4159_, v_maxFVars_x3f_4160_, v_k_4161_, v_cleanupAnnotations_boxed_4169_, v_whnfType_boxed_4170_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4172_, lean_object* v_type_4173_, lean_object* v_maxFVars_x3f_4174_, lean_object* v_k_4175_, uint8_t v_cleanupAnnotations_4176_, uint8_t v_whnfType_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4173_, v_maxFVars_x3f_4174_, v_k_4175_, v_cleanupAnnotations_4176_, v_whnfType_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4184_, lean_object* v_type_4185_, lean_object* v_maxFVars_x3f_4186_, lean_object* v_k_4187_, lean_object* v_cleanupAnnotations_4188_, lean_object* v_whnfType_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4195_; uint8_t v_whnfType_boxed_4196_; lean_object* v_res_4197_; 
v_cleanupAnnotations_boxed_4195_ = lean_unbox(v_cleanupAnnotations_4188_);
v_whnfType_boxed_4196_ = lean_unbox(v_whnfType_4189_);
v_res_4197_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4184_, v_type_4185_, v_maxFVars_x3f_4186_, v_k_4187_, v_cleanupAnnotations_boxed_4195_, v_whnfType_boxed_4196_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4198_, lean_object* v_recArgInfos_4199_, lean_object* v_positions_4200_, lean_object* v_value_4201_, lean_object* v_fst_4202_, lean_object* v_snd_4203_, lean_object* v_below_4204_, lean_object* v_x_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = lean_array_get_borrowed(v___x_4198_, v_below_4204_, v___x_4211_);
lean_inc(v___x_4212_);
v___x_4213_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4199_, v_positions_4200_, v___x_4212_, v_value_4201_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; uint8_t v___x_4221_; uint8_t v___x_4222_; lean_object* v___x_4223_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
v___x_4215_ = lean_unsigned_to_nat(1u);
v___x_4216_ = lean_mk_empty_array_with_capacity(v___x_4215_);
lean_inc(v___x_4212_);
v___x_4217_ = lean_array_push(v___x_4216_, v___x_4212_);
v___x_4218_ = l_Array_append___redArg(v_fst_4202_, v___x_4217_);
lean_dec_ref(v___x_4217_);
v___x_4219_ = l_Array_append___redArg(v___x_4218_, v_snd_4203_);
v___x_4220_ = 0;
v___x_4221_ = 1;
v___x_4222_ = 1;
v___x_4223_ = l_Lean_Meta_mkLambdaFVars(v___x_4219_, v_a_4214_, v___x_4220_, v___x_4221_, v___x_4220_, v___x_4221_, v___x_4222_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec_ref(v___x_4219_);
return v___x_4223_;
}
else
{
lean_dec_ref(v_fst_4202_);
return v___x_4213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4224_, lean_object* v_recArgInfos_4225_, lean_object* v_positions_4226_, lean_object* v_value_4227_, lean_object* v_fst_4228_, lean_object* v_snd_4229_, lean_object* v_below_4230_, lean_object* v_x_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4224_, v_recArgInfos_4225_, v_positions_4226_, v_value_4227_, v_fst_4228_, v_snd_4229_, v_below_4230_, v_x_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec_ref(v_x_4231_);
lean_dec_ref(v_below_4230_);
lean_dec_ref(v_snd_4229_);
lean_dec_ref(v___x_4224_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4240_, lean_object* v_FType_4241_, lean_object* v___x_4242_, lean_object* v_recArgInfos_4243_, lean_object* v_positions_4244_, lean_object* v_xs_4245_, lean_object* v_value_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; lean_object* v_fst_4253_; lean_object* v_snd_4254_; lean_object* v___x_4255_; 
v___x_4252_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4240_, v_xs_4245_);
v_fst_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_fst_4253_);
v_snd_4254_ = lean_ctor_get(v___x_4252_, 1);
lean_inc(v_snd_4254_);
lean_dec_ref(v___x_4252_);
v___x_4255_ = l_Lean_Meta_instantiateForall(v_FType_4241_, v_fst_4253_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___f_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___f_4257_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4257_, 0, v___x_4242_);
lean_closure_set(v___f_4257_, 1, v_recArgInfos_4243_);
lean_closure_set(v___f_4257_, 2, v_positions_4244_);
lean_closure_set(v___f_4257_, 3, v_value_4246_);
lean_closure_set(v___f_4257_, 4, v_fst_4253_);
lean_closure_set(v___f_4257_, 5, v_snd_4254_);
v___x_4258_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4259_ = 0;
v___x_4260_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4256_, v___x_4258_, v___f_4257_, v___x_4259_, v___x_4259_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
return v___x_4260_;
}
else
{
lean_dec(v_snd_4254_);
lean_dec(v_fst_4253_);
lean_dec_ref(v_value_4246_);
lean_dec_ref(v_positions_4244_);
lean_dec_ref(v_recArgInfos_4243_);
lean_dec_ref(v___x_4242_);
return v___x_4255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4261_, lean_object* v_FType_4262_, lean_object* v___x_4263_, lean_object* v_recArgInfos_4264_, lean_object* v_positions_4265_, lean_object* v_xs_4266_, lean_object* v_value_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4261_, v_FType_4262_, v___x_4263_, v_recArgInfos_4264_, v_positions_4265_, v_xs_4266_, v_value_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4274_, lean_object* v_positions_4275_, lean_object* v_recArgInfo_4276_, lean_object* v_value_4277_, lean_object* v_FType_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v___x_4284_; lean_object* v___f_4285_; uint8_t v___x_4286_; lean_object* v___x_4287_; 
v___x_4284_ = l_Lean_instInhabitedExpr;
v___f_4285_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4285_, 0, v_recArgInfo_4276_);
lean_closure_set(v___f_4285_, 1, v_FType_4278_);
lean_closure_set(v___f_4285_, 2, v___x_4284_);
lean_closure_set(v___f_4285_, 3, v_recArgInfos_4274_);
lean_closure_set(v___f_4285_, 4, v_positions_4275_);
v___x_4286_ = 0;
v___x_4287_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4277_, v___f_4285_, v___x_4286_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4288_, lean_object* v_positions_4289_, lean_object* v_recArgInfo_4290_, lean_object* v_value_4291_, lean_object* v_FType_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4288_, v_positions_4289_, v_recArgInfo_4290_, v_value_4291_, v_FType_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4299_, lean_object* v_params_4300_, uint8_t v_isIndPred_4301_, lean_object* v_brecOnUniv_4302_, lean_object* v_levels_4303_, lean_object* v_idx_4304_){
_start:
{
lean_object* v_n_4305_; lean_object* v___y_4307_; 
v_n_4305_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4299_, v_idx_4304_);
if (v_isIndPred_4301_ == 0)
{
lean_object* v___x_4310_; 
v___x_4310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4310_, 0, v_brecOnUniv_4302_);
lean_ctor_set(v___x_4310_, 1, v_levels_4303_);
v___y_4307_ = v___x_4310_;
goto v___jp_4306_;
}
else
{
lean_dec(v_brecOnUniv_4302_);
v___y_4307_ = v_levels_4303_;
goto v___jp_4306_;
}
v___jp_4306_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = l_Lean_Expr_const___override(v_n_4305_, v___y_4307_);
v___x_4309_ = l_Lean_mkAppN(v___x_4308_, v_params_4300_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4311_, lean_object* v_params_4312_, lean_object* v_isIndPred_4313_, lean_object* v_brecOnUniv_4314_, lean_object* v_levels_4315_, lean_object* v_idx_4316_){
_start:
{
uint8_t v_isIndPred_boxed_4317_; lean_object* v_res_4318_; 
v_isIndPred_boxed_4317_ = lean_unbox(v_isIndPred_4313_);
v_res_4318_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4311_, v_params_4312_, v_isIndPred_boxed_4317_, v_brecOnUniv_4314_, v_levels_4315_, v_idx_4316_);
lean_dec(v_idx_4316_);
lean_dec_ref(v_params_4312_);
lean_dec_ref(v_toIndGroupInfo_4311_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4319_, lean_object* v_a_4320_, lean_object* v_n_4321_){
_start:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4322_ = lean_apply_1(v_brecOnCons_4319_, v_n_4321_);
v___x_4323_ = l_Lean_mkAppN(v___x_4322_, v_a_4320_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4324_, lean_object* v_a_4325_, lean_object* v_n_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4324_, v_a_4325_, v_n_4326_);
lean_dec_ref(v_a_4325_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4328_, lean_object* v_type_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l_Lean_Meta_getLevel(v_type_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4336_, lean_object* v_type_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4336_, v_type_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec_ref(v_x_4336_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4344_, size_t v_sz_4345_, size_t v_i_4346_, lean_object* v_bs_4347_){
_start:
{
uint8_t v___x_4348_; 
v___x_4348_ = lean_usize_dec_lt(v_i_4346_, v_sz_4345_);
if (v___x_4348_ == 0)
{
return v_bs_4347_;
}
else
{
lean_object* v___x_4349_; lean_object* v_v_4350_; lean_object* v___x_4351_; lean_object* v_bs_x27_4352_; lean_object* v___x_4353_; size_t v___x_4354_; size_t v___x_4355_; lean_object* v___x_4356_; 
v___x_4349_ = l_Lean_instInhabitedExpr;
v_v_4350_ = lean_array_uget(v_bs_4347_, v_i_4346_);
v___x_4351_ = lean_unsigned_to_nat(0u);
v_bs_x27_4352_ = lean_array_uset(v_bs_4347_, v_i_4346_, v___x_4351_);
v___x_4353_ = lean_array_get_borrowed(v___x_4349_, v_xs_4344_, v_v_4350_);
lean_dec(v_v_4350_);
v___x_4354_ = ((size_t)1ULL);
v___x_4355_ = lean_usize_add(v_i_4346_, v___x_4354_);
lean_inc(v___x_4353_);
v___x_4356_ = lean_array_uset(v_bs_x27_4352_, v_i_4346_, v___x_4353_);
v_i_4346_ = v___x_4355_;
v_bs_4347_ = v___x_4356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4358_, lean_object* v_sz_4359_, lean_object* v_i_4360_, lean_object* v_bs_4361_){
_start:
{
size_t v_sz_boxed_4362_; size_t v_i_boxed_4363_; lean_object* v_res_4364_; 
v_sz_boxed_4362_ = lean_unbox_usize(v_sz_4359_);
lean_dec(v_sz_4359_);
v_i_boxed_4363_ = lean_unbox_usize(v_i_4360_);
lean_dec(v_i_4360_);
v_res_4364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4358_, v_sz_boxed_4362_, v_i_boxed_4363_, v_bs_4361_);
lean_dec_ref(v_xs_4358_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4365_, lean_object* v_f_4366_, lean_object* v_as_4367_, lean_object* v_bs_4368_, lean_object* v_i_4369_, lean_object* v_cs_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v___x_4376_; uint8_t v___x_4377_; 
v___x_4376_ = lean_array_get_size(v_as_4367_);
v___x_4377_ = lean_nat_dec_lt(v_i_4369_, v___x_4376_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4378_; 
lean_dec(v_i_4369_);
lean_dec_ref(v_f_4366_);
v___x_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4378_, 0, v_cs_4370_);
return v___x_4378_;
}
else
{
lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4379_ = lean_array_get_size(v_bs_4368_);
v___x_4380_ = lean_nat_dec_lt(v_i_4369_, v___x_4379_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; 
lean_dec(v_i_4369_);
lean_dec_ref(v_f_4366_);
v___x_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4381_, 0, v_cs_4370_);
return v___x_4381_;
}
else
{
lean_object* v_a_4382_; lean_object* v_b_4383_; size_t v_sz_4384_; size_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_a_4382_ = lean_array_fget_borrowed(v_as_4367_, v_i_4369_);
v_b_4383_ = lean_array_fget_borrowed(v_bs_4368_, v_i_4369_);
v_sz_4384_ = lean_array_size(v_b_4383_);
v___x_4385_ = ((size_t)0ULL);
lean_inc(v_b_4383_);
v___x_4386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4365_, v_sz_4384_, v___x_4385_, v_b_4383_);
lean_inc_ref(v_f_4366_);
lean_inc(v___y_4374_);
lean_inc_ref(v___y_4373_);
lean_inc(v___y_4372_);
lean_inc_ref(v___y_4371_);
lean_inc(v_a_4382_);
v___x_4387_ = lean_apply_7(v_f_4366_, v_a_4382_, v___x_4386_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, lean_box(0));
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref_known(v___x_4387_, 1);
v___x_4389_ = lean_unsigned_to_nat(1u);
v___x_4390_ = lean_nat_add(v_i_4369_, v___x_4389_);
lean_dec(v_i_4369_);
v___x_4391_ = lean_array_push(v_cs_4370_, v_a_4388_);
v_i_4369_ = v___x_4390_;
v_cs_4370_ = v___x_4391_;
goto _start;
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec_ref(v_cs_4370_);
lean_dec(v_i_4369_);
lean_dec_ref(v_f_4366_);
v_a_4393_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4387_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4387_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4401_, lean_object* v_f_4402_, lean_object* v_as_4403_, lean_object* v_bs_4404_, lean_object* v_i_4405_, lean_object* v_cs_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4401_, v_f_4402_, v_as_4403_, v_bs_4404_, v_i_4405_, v_cs_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec_ref(v_bs_4404_);
lean_dec_ref(v_as_4403_);
lean_dec_ref(v_xs_4401_);
return v_res_4412_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = l_Array_instInhabited(lean_box(0));
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; lean_object* v_toApplicative_4421_; lean_object* v_toFunctor_4422_; lean_object* v_toSeq_4423_; lean_object* v_toSeqLeft_4424_; lean_object* v_toSeqRight_4425_; lean_object* v___f_4426_; lean_object* v___f_4427_; lean_object* v___f_4428_; lean_object* v___f_4429_; lean_object* v___x_4430_; lean_object* v___f_4431_; lean_object* v___f_4432_; lean_object* v___f_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v_toApplicative_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4468_; 
v___x_4420_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4421_ = lean_ctor_get(v___x_4420_, 0);
v_toFunctor_4422_ = lean_ctor_get(v_toApplicative_4421_, 0);
v_toSeq_4423_ = lean_ctor_get(v_toApplicative_4421_, 2);
v_toSeqLeft_4424_ = lean_ctor_get(v_toApplicative_4421_, 3);
v_toSeqRight_4425_ = lean_ctor_get(v_toApplicative_4421_, 4);
v___f_4426_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4427_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4422_, 2);
v___f_4428_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4428_, 0, v_toFunctor_4422_);
v___f_4429_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4429_, 0, v_toFunctor_4422_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___f_4428_);
lean_ctor_set(v___x_4430_, 1, v___f_4429_);
lean_inc(v_toSeqRight_4425_);
v___f_4431_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4431_, 0, v_toSeqRight_4425_);
lean_inc(v_toSeqLeft_4424_);
v___f_4432_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4432_, 0, v_toSeqLeft_4424_);
lean_inc(v_toSeq_4423_);
v___f_4433_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4433_, 0, v_toSeq_4423_);
v___x_4434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4430_);
lean_ctor_set(v___x_4434_, 1, v___f_4426_);
lean_ctor_set(v___x_4434_, 2, v___f_4433_);
lean_ctor_set(v___x_4434_, 3, v___f_4432_);
lean_ctor_set(v___x_4434_, 4, v___f_4431_);
v___x_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
lean_ctor_set(v___x_4435_, 1, v___f_4427_);
v___x_4436_ = l_StateRefT_x27_instMonad___redArg(v___x_4435_);
v_toApplicative_4437_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4468_ == 0)
{
lean_object* v_unused_4469_; 
v_unused_4469_ = lean_ctor_get(v___x_4436_, 1);
lean_dec(v_unused_4469_);
v___x_4439_ = v___x_4436_;
v_isShared_4440_ = v_isSharedCheck_4468_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_toApplicative_4437_);
lean_dec(v___x_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4468_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v_toFunctor_4441_; lean_object* v_toSeq_4442_; lean_object* v_toSeqLeft_4443_; lean_object* v_toSeqRight_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4466_; 
v_toFunctor_4441_ = lean_ctor_get(v_toApplicative_4437_, 0);
v_toSeq_4442_ = lean_ctor_get(v_toApplicative_4437_, 2);
v_toSeqLeft_4443_ = lean_ctor_get(v_toApplicative_4437_, 3);
v_toSeqRight_4444_ = lean_ctor_get(v_toApplicative_4437_, 4);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_toApplicative_4437_);
if (v_isSharedCheck_4466_ == 0)
{
lean_object* v_unused_4467_; 
v_unused_4467_ = lean_ctor_get(v_toApplicative_4437_, 1);
lean_dec(v_unused_4467_);
v___x_4446_ = v_toApplicative_4437_;
v_isShared_4447_ = v_isSharedCheck_4466_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_toSeqRight_4444_);
lean_inc(v_toSeqLeft_4443_);
lean_inc(v_toSeq_4442_);
lean_inc(v_toFunctor_4441_);
lean_dec(v_toApplicative_4437_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4466_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___f_4448_; lean_object* v___f_4449_; lean_object* v___f_4450_; lean_object* v___f_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___f_4454_; lean_object* v___f_4455_; lean_object* v___x_4457_; 
v___f_4448_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4449_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4441_);
v___f_4450_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4450_, 0, v_toFunctor_4441_);
v___f_4451_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4451_, 0, v_toFunctor_4441_);
v___x_4452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___f_4450_);
lean_ctor_set(v___x_4452_, 1, v___f_4451_);
v___f_4453_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4453_, 0, v_toSeqRight_4444_);
v___f_4454_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4454_, 0, v_toSeqLeft_4443_);
v___f_4455_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4455_, 0, v_toSeq_4442_);
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 4, v___f_4453_);
lean_ctor_set(v___x_4446_, 3, v___f_4454_);
lean_ctor_set(v___x_4446_, 2, v___f_4455_);
lean_ctor_set(v___x_4446_, 1, v___f_4448_);
lean_ctor_set(v___x_4446_, 0, v___x_4452_);
v___x_4457_ = v___x_4446_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4452_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v___f_4448_);
lean_ctor_set(v_reuseFailAlloc_4465_, 2, v___f_4455_);
lean_ctor_set(v_reuseFailAlloc_4465_, 3, v___f_4454_);
lean_ctor_set(v_reuseFailAlloc_4465_, 4, v___f_4453_);
v___x_4457_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4459_; 
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 1, v___f_4449_);
lean_ctor_set(v___x_4439_, 0, v___x_4457_);
v___x_4459_ = v___x_4439_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v___f_4449_);
v___x_4459_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_940__overap_4462_; lean_object* v___x_4463_; 
v___x_4460_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4461_ = l_instInhabitedOfMonad___redArg(v___x_4459_, v___x_4460_);
v___x_940__overap_4462_ = lean_panic_fn_borrowed(v___x_4461_, v_msg_4414_);
lean_dec(v___x_4461_);
lean_inc(v___y_4418_);
lean_inc_ref(v___y_4417_);
lean_inc(v___y_4416_);
lean_inc_ref(v___y_4415_);
v___x_4463_ = lean_apply_5(v___x_940__overap_4462_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, lean_box(0));
return v___x_4463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
return v_res_4476_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4480_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4481_ = lean_unsigned_to_nat(2u);
v___x_4482_ = lean_unsigned_to_nat(73u);
v___x_4483_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4484_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4485_ = l_mkPanicMessageWithDecl(v___x_4484_, v___x_4483_, v___x_4482_, v___x_4481_, v___x_4480_);
return v___x_4485_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4487_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4488_ = lean_unsigned_to_nat(2u);
v___x_4489_ = lean_unsigned_to_nat(74u);
v___x_4490_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4491_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4492_ = l_mkPanicMessageWithDecl(v___x_4491_, v___x_4490_, v___x_4489_, v___x_4488_, v___x_4487_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4495_, lean_object* v_positions_4496_, lean_object* v_ys_4497_, lean_object* v_xs_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; uint8_t v___x_4506_; 
v___x_4504_ = lean_array_get_size(v_positions_4496_);
v___x_4505_ = lean_array_get_size(v_ys_4497_);
v___x_4506_ = lean_nat_dec_eq(v___x_4504_, v___x_4505_);
if (v___x_4506_ == 0)
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
lean_dec_ref(v_f_4495_);
v___x_4507_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4508_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4507_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
return v___x_4508_;
}
else
{
lean_object* v___x_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4509_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4496_);
v___x_4510_ = lean_array_get_size(v_xs_4498_);
v___x_4511_ = lean_nat_dec_eq(v___x_4509_, v___x_4510_);
lean_dec(v___x_4509_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; lean_object* v___x_4513_; 
lean_dec_ref(v_f_4495_);
v___x_4512_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4513_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4512_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
return v___x_4513_;
}
else
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4514_ = lean_unsigned_to_nat(0u);
v___x_4515_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4516_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4498_, v_f_4495_, v_ys_4497_, v_positions_4496_, v___x_4514_, v___x_4515_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
return v___x_4516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4517_, lean_object* v_positions_4518_, lean_object* v_ys_4519_, lean_object* v_xs_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4517_, v_positions_4518_, v_ys_4519_, v_xs_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec_ref(v_xs_4520_);
lean_dec_ref(v_ys_4519_);
lean_dec_ref(v_positions_4518_);
return v_res_4526_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = lean_unsigned_to_nat(0u);
v___x_4529_ = l_Lean_Level_ofNat(v___x_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4530_, lean_object* v_positions_4531_, lean_object* v_motives_4532_, uint8_t v_isIndPred_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v_indGroupInst_4542_; lean_object* v_brecOnUniv_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; 
v___x_4539_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4540_ = lean_unsigned_to_nat(0u);
v___x_4541_ = lean_array_get_borrowed(v___x_4539_, v_recArgInfos_4530_, v___x_4540_);
v_indGroupInst_4542_ = lean_ctor_get(v___x_4541_, 4);
if (v_isIndPred_4533_ == 0)
{
lean_object* v___f_4585_; lean_object* v___x_4586_; lean_object* v_motive_4587_; lean_object* v___x_4588_; 
v___f_4585_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4586_ = l_Lean_instInhabitedExpr;
v_motive_4587_ = lean_array_get_borrowed(v___x_4586_, v_motives_4532_, v___x_4540_);
lean_inc(v_motive_4587_);
v___x_4588_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4587_, v___f_4585_, v_isIndPred_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
if (lean_obj_tag(v___x_4588_) == 0)
{
lean_object* v_a_4589_; 
v_a_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc(v_a_4589_);
lean_dec_ref_known(v___x_4588_, 1);
v_brecOnUniv_4544_ = v_a_4589_;
v___y_4545_ = v_a_4534_;
v___y_4546_ = v_a_4535_;
v___y_4547_ = v_a_4536_;
v___y_4548_ = v_a_4537_;
goto v___jp_4543_;
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
v_a_4590_ = lean_ctor_get(v___x_4588_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4588_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4588_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
else
{
lean_object* v___x_4598_; 
v___x_4598_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4544_ = v___x_4598_;
v___y_4545_ = v_a_4534_;
v___y_4546_ = v_a_4535_;
v___y_4547_ = v_a_4536_;
v___y_4548_ = v_a_4537_;
goto v___jp_4543_;
}
v___jp_4543_:
{
lean_object* v_toIndGroupInfo_4549_; lean_object* v_levels_4550_; lean_object* v_params_4551_; lean_object* v___x_4552_; lean_object* v_brecOnCons_4553_; lean_object* v_brecOnAux_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v_toIndGroupInfo_4549_ = lean_ctor_get(v_indGroupInst_4542_, 0);
v_levels_4550_ = lean_ctor_get(v_indGroupInst_4542_, 1);
v_params_4551_ = lean_ctor_get(v_indGroupInst_4542_, 2);
v___x_4552_ = lean_box(v_isIndPred_4533_);
lean_inc_n(v_levels_4550_, 2);
lean_inc(v_brecOnUniv_4544_);
lean_inc_ref(v_params_4551_);
lean_inc_ref(v_toIndGroupInfo_4549_);
v_brecOnCons_4553_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4553_, 0, v_toIndGroupInfo_4549_);
lean_closure_set(v_brecOnCons_4553_, 1, v_params_4551_);
lean_closure_set(v_brecOnCons_4553_, 2, v___x_4552_);
lean_closure_set(v_brecOnCons_4553_, 3, v_brecOnUniv_4544_);
lean_closure_set(v_brecOnCons_4553_, 4, v_levels_4550_);
v_brecOnAux_4554_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4549_, v_params_4551_, v_isIndPred_4533_, v_brecOnUniv_4544_, v_levels_4550_, v___x_4540_);
v___x_4555_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4549_);
v___x_4556_ = l_Lean_Meta_inferArgumentTypesN(v___x_4555_, v_brecOnAux_4554_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v___x_4556_, 1);
v___x_4558_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4559_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4558_, v_positions_4531_, v_a_4557_, v_motives_4532_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v_a_4557_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4568_; 
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4562_ = v___x_4559_;
v_isShared_4563_ = v_isSharedCheck_4568_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4559_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4568_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___f_4564_; lean_object* v___x_4566_; 
v___f_4564_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4564_, 0, v_brecOnCons_4553_);
lean_closure_set(v___f_4564_, 1, v_a_4560_);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 0, v___f_4564_);
v___x_4566_ = v___x_4562_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___f_4564_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_dec_ref(v_brecOnCons_4553_);
v_a_4569_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4559_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4559_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec_ref(v_brecOnCons_4553_);
v_a_4577_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4556_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4556_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4599_, lean_object* v_positions_4600_, lean_object* v_motives_4601_, lean_object* v_isIndPred_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
uint8_t v_isIndPred_boxed_4608_; lean_object* v_res_4609_; 
v_isIndPred_boxed_4608_ = lean_unbox(v_isIndPred_4602_);
v_res_4609_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4599_, v_positions_4600_, v_motives_4601_, v_isIndPred_boxed_4608_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
lean_dec(v_a_4604_);
lean_dec_ref(v_a_4603_);
lean_dec_ref(v_motives_4601_);
lean_dec_ref(v_positions_4600_);
lean_dec_ref(v_recArgInfos_4599_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4610_, lean_object* v_msg_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4618_, lean_object* v_msg_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4618_, v_msg_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4626_, lean_object* v_00_u03b1_4627_, lean_object* v_f_4628_, lean_object* v_positions_4629_, lean_object* v_ys_4630_, lean_object* v_xs_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4628_, v_positions_4629_, v_ys_4630_, v_xs_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4638_, lean_object* v_00_u03b1_4639_, lean_object* v_f_4640_, lean_object* v_positions_4641_, lean_object* v_ys_4642_, lean_object* v_xs_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4638_, v_00_u03b1_4639_, v_f_4640_, v_positions_4641_, v_ys_4642_, v_xs_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec_ref(v_xs_4643_);
lean_dec_ref(v_ys_4642_);
lean_dec_ref(v_positions_4641_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4650_, lean_object* v_00_u03b3_4651_, lean_object* v_xs_4652_, lean_object* v_f_4653_, lean_object* v_as_4654_, lean_object* v_bs_4655_, lean_object* v_i_4656_, lean_object* v_cs_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v___x_4663_; 
v___x_4663_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4652_, v_f_4653_, v_as_4654_, v_bs_4655_, v_i_4656_, v_cs_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4664_, lean_object* v_00_u03b3_4665_, lean_object* v_xs_4666_, lean_object* v_f_4667_, lean_object* v_as_4668_, lean_object* v_bs_4669_, lean_object* v_i_4670_, lean_object* v_cs_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4664_, v_00_u03b3_4665_, v_xs_4666_, v_f_4667_, v_as_4668_, v_bs_4669_, v_i_4670_, v_cs_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec_ref(v_bs_4669_);
lean_dec_ref(v_as_4668_);
lean_dec_ref(v_xs_4666_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_4678_, lean_object* v_e_4679_){
_start:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = l_Lean_indentD(v_e_4679_);
v___x_4681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4678_);
lean_ctor_set(v___x_4681_, 1, v___x_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_4682_, lean_object* v_x_4683_, lean_object* v_brecOnType_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4682_, v_brecOnType_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_4691_, lean_object* v_x_4692_, lean_object* v_brecOnType_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_4691_, v_x_4692_, v_brecOnType_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec_ref(v_x_4692_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4700_, lean_object* v_as_4701_, size_t v_sz_4702_, size_t v_i_4703_, lean_object* v_b_4704_){
_start:
{
uint8_t v___x_4706_; 
v___x_4706_ = lean_usize_dec_lt(v_i_4703_, v_sz_4702_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4707_; 
lean_dec_ref(v_a_4700_);
v___x_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4707_, 0, v_b_4704_);
return v___x_4707_;
}
else
{
lean_object* v_a_4708_; lean_object* v___x_4709_; size_t v___x_4710_; size_t v___x_4711_; 
v_a_4708_ = lean_array_uget_borrowed(v_as_4701_, v_i_4703_);
lean_inc_ref(v_a_4700_);
v___x_4709_ = lean_array_set(v_b_4704_, v_a_4708_, v_a_4700_);
v___x_4710_ = ((size_t)1ULL);
v___x_4711_ = lean_usize_add(v_i_4703_, v___x_4710_);
v_i_4703_ = v___x_4711_;
v_b_4704_ = v___x_4709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4713_, lean_object* v_as_4714_, lean_object* v_sz_4715_, lean_object* v_i_4716_, lean_object* v_b_4717_, lean_object* v___y_4718_){
_start:
{
size_t v_sz_boxed_4719_; size_t v_i_boxed_4720_; lean_object* v_res_4721_; 
v_sz_boxed_4719_ = lean_unbox_usize(v_sz_4715_);
lean_dec(v_sz_4715_);
v_i_boxed_4720_ = lean_unbox_usize(v_i_4716_);
lean_dec(v_i_4716_);
v_res_4721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4713_, v_as_4714_, v_sz_boxed_4719_, v_i_boxed_4720_, v_b_4717_);
lean_dec_ref(v_as_4714_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4722_, size_t v_sz_4723_, size_t v_i_4724_, lean_object* v_b_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
uint8_t v___x_4731_; 
v___x_4731_ = lean_usize_dec_lt(v_i_4724_, v_sz_4723_);
if (v___x_4731_ == 0)
{
lean_object* v___x_4732_; 
v___x_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4732_, 0, v_b_4725_);
return v___x_4732_;
}
else
{
lean_object* v_snd_4733_; lean_object* v_fst_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4778_; 
v_snd_4733_ = lean_ctor_get(v_b_4725_, 1);
v_fst_4734_ = lean_ctor_get(v_b_4725_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v_b_4725_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4736_ = v_b_4725_;
v_isShared_4737_ = v_isSharedCheck_4778_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_snd_4733_);
lean_inc(v_fst_4734_);
lean_dec(v_b_4725_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4778_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v_array_4738_; lean_object* v_start_4739_; lean_object* v_stop_4740_; uint8_t v___x_4741_; 
v_array_4738_ = lean_ctor_get(v_snd_4733_, 0);
v_start_4739_ = lean_ctor_get(v_snd_4733_, 1);
v_stop_4740_ = lean_ctor_get(v_snd_4733_, 2);
v___x_4741_ = lean_nat_dec_lt(v_start_4739_, v_stop_4740_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4743_; 
if (v_isShared_4737_ == 0)
{
v___x_4743_ = v___x_4736_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_fst_4734_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_snd_4733_);
v___x_4743_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4744_; 
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
else
{
lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4774_; 
lean_inc(v_stop_4740_);
lean_inc(v_start_4739_);
lean_inc_ref(v_array_4738_);
v_isSharedCheck_4774_ = !lean_is_exclusive(v_snd_4733_);
if (v_isSharedCheck_4774_ == 0)
{
lean_object* v_unused_4775_; lean_object* v_unused_4776_; lean_object* v_unused_4777_; 
v_unused_4775_ = lean_ctor_get(v_snd_4733_, 2);
lean_dec(v_unused_4775_);
v_unused_4776_ = lean_ctor_get(v_snd_4733_, 1);
lean_dec(v_unused_4776_);
v_unused_4777_ = lean_ctor_get(v_snd_4733_, 0);
lean_dec(v_unused_4777_);
v___x_4747_ = v_snd_4733_;
v_isShared_4748_ = v_isSharedCheck_4774_;
goto v_resetjp_4746_;
}
else
{
lean_dec(v_snd_4733_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4774_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v_a_4749_; lean_object* v___x_4750_; size_t v_sz_4751_; size_t v___x_4752_; lean_object* v___x_4753_; 
v_a_4749_ = lean_array_uget_borrowed(v_as_4722_, v_i_4724_);
v___x_4750_ = lean_array_fget_borrowed(v_array_4738_, v_start_4739_);
v_sz_4751_ = lean_array_size(v___x_4750_);
v___x_4752_ = ((size_t)0ULL);
lean_inc(v_a_4749_);
v___x_4753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4749_, v___x_4750_, v_sz_4751_, v___x_4752_, v_fst_4734_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v_a_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
lean_inc(v_a_4754_);
lean_dec_ref_known(v___x_4753_, 1);
v___x_4755_ = lean_unsigned_to_nat(1u);
v___x_4756_ = lean_nat_add(v_start_4739_, v___x_4755_);
lean_dec(v_start_4739_);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 1, v___x_4756_);
v___x_4758_ = v___x_4747_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_array_4738_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v___x_4756_);
lean_ctor_set(v_reuseFailAlloc_4765_, 2, v_stop_4740_);
v___x_4758_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4760_; 
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 1, v___x_4758_);
lean_ctor_set(v___x_4736_, 0, v_a_4754_);
v___x_4760_ = v___x_4736_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4754_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v___x_4758_);
v___x_4760_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
size_t v___x_4761_; size_t v___x_4762_; 
v___x_4761_ = ((size_t)1ULL);
v___x_4762_ = lean_usize_add(v_i_4724_, v___x_4761_);
v_i_4724_ = v___x_4762_;
v_b_4725_ = v___x_4760_;
goto _start;
}
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_del_object(v___x_4747_);
lean_dec(v_stop_4740_);
lean_dec(v_start_4739_);
lean_dec_ref(v_array_4738_);
lean_del_object(v___x_4736_);
v_a_4766_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4753_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4753_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4779_, lean_object* v_sz_4780_, lean_object* v_i_4781_, lean_object* v_b_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
size_t v_sz_boxed_4788_; size_t v_i_boxed_4789_; lean_object* v_res_4790_; 
v_sz_boxed_4788_ = lean_unbox_usize(v_sz_4780_);
lean_dec(v_sz_4780_);
v_i_boxed_4789_ = lean_unbox_usize(v_i_4781_);
lean_dec(v_i_4781_);
v_res_4790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4779_, v_sz_boxed_4788_, v_i_boxed_4789_, v_b_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec_ref(v_as_4779_);
return v_res_4790_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4793_ = l_Lean_stringToMessageData(v___x_4792_);
return v___x_4793_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4794_; lean_object* v___f_4795_; 
v___x_4794_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4795_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_4795_, 0, v___x_4794_);
return v___f_4795_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4797_ = l_Lean_Expr_sort___override(v___x_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4798_, lean_object* v_positions_4799_, lean_object* v_brecOnConst_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v_recArgInfo_4808_; lean_object* v_indicesPos_4809_; lean_object* v_indIdx_4810_; lean_object* v_brecOn_4811_; lean_object* v___f_4812_; uint8_t v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4806_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4807_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4808_ = lean_array_get_borrowed(v___x_4806_, v_recArgInfos_4798_, v___x_4807_);
v_indicesPos_4809_ = lean_ctor_get(v_recArgInfo_4808_, 3);
v_indIdx_4810_ = lean_ctor_get(v_recArgInfo_4808_, 5);
lean_inc(v_indIdx_4810_);
v_brecOn_4811_ = lean_apply_1(v_brecOnConst_4800_, v_indIdx_4810_);
v___f_4812_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4813_ = 0;
v___x_4814_ = lean_box(v___x_4813_);
lean_inc_ref(v_brecOn_4811_);
v___x_4815_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4815_, 0, v_brecOn_4811_);
lean_closure_set(v___x_4815_, 1, v___x_4814_);
v___x_4816_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4815_, v___f_4812_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v___x_4817_; 
lean_dec_ref_known(v___x_4816_, 1);
lean_inc(v_a_4804_);
lean_inc_ref(v_a_4803_);
lean_inc(v_a_4802_);
lean_inc_ref(v_a_4801_);
v___x_4817_ = lean_infer_type(v_brecOn_4811_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v_numTypeFormers_4819_; lean_object* v___f_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; uint8_t v___x_4825_; lean_object* v___x_4826_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc(v_a_4818_);
lean_dec_ref_known(v___x_4817_, 1);
v_numTypeFormers_4819_ = lean_array_get_size(v_positions_4799_);
v___f_4820_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4820_, 0, v_numTypeFormers_4819_);
v___x_4821_ = lean_array_get_size(v_indicesPos_4809_);
v___x_4822_ = lean_unsigned_to_nat(1u);
v___x_4823_ = lean_nat_add(v___x_4821_, v___x_4822_);
v___x_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4823_);
v___x_4825_ = 0;
v___x_4826_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4818_, v___x_4824_, v___f_4820_, v___x_4825_, v___x_4825_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v_a_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; size_t v_sz_4833_; size_t v___x_4834_; lean_object* v___x_4835_; 
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref_known(v___x_4826_, 1);
v___x_4828_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4799_);
v___x_4829_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4830_ = lean_mk_array(v___x_4828_, v___x_4829_);
v___x_4831_ = l_Array_toSubarray___redArg(v_positions_4799_, v___x_4807_, v_numTypeFormers_4819_);
v___x_4832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4830_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
v_sz_4833_ = lean_array_size(v_a_4827_);
v___x_4834_ = ((size_t)0ULL);
v___x_4835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4827_, v_sz_4833_, v___x_4834_, v___x_4832_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
lean_dec(v_a_4827_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4844_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4838_ = v___x_4835_;
v_isShared_4839_ = v_isSharedCheck_4844_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4835_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4844_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v_fst_4840_; lean_object* v___x_4842_; 
v_fst_4840_ = lean_ctor_get(v_a_4836_, 0);
lean_inc(v_fst_4840_);
lean_dec(v_a_4836_);
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v_fst_4840_);
v___x_4842_ = v___x_4838_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_fst_4840_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
else
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4852_; 
v_a_4845_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4847_ = v___x_4835_;
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4835_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4850_; 
if (v_isShared_4848_ == 0)
{
v___x_4850_ = v___x_4847_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4799_);
return v___x_4826_;
}
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec_ref(v_positions_4799_);
v_a_4853_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4817_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4817_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
lean_dec_ref(v_brecOn_4811_);
lean_dec_ref(v_positions_4799_);
v_a_4861_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4816_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4816_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4869_, lean_object* v_positions_4870_, lean_object* v_brecOnConst_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4869_, v_positions_4870_, v_brecOnConst_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
lean_dec(v_a_4875_);
lean_dec_ref(v_a_4874_);
lean_dec(v_a_4873_);
lean_dec_ref(v_a_4872_);
lean_dec_ref(v_recArgInfos_4869_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4878_, lean_object* v_as_4879_, size_t v_sz_4880_, size_t v_i_4881_, lean_object* v_b_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4878_, v_as_4879_, v_sz_4880_, v_i_4881_, v_b_4882_);
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4889_, lean_object* v_as_4890_, lean_object* v_sz_4891_, lean_object* v_i_4892_, lean_object* v_b_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
size_t v_sz_boxed_4899_; size_t v_i_boxed_4900_; lean_object* v_res_4901_; 
v_sz_boxed_4899_ = lean_unbox_usize(v_sz_4891_);
lean_dec(v_sz_4891_);
v_i_boxed_4900_ = lean_unbox_usize(v_i_4892_);
lean_dec(v_i_4892_);
v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4889_, v_as_4890_, v_sz_boxed_4899_, v_i_boxed_4900_, v_b_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec_ref(v_as_4890_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
if (lean_obj_tag(v_a_4902_) == 0)
{
lean_object* v___x_4904_; 
v___x_4904_ = l_List_reverse___redArg(v_a_4903_);
return v___x_4904_;
}
else
{
lean_object* v_head_4905_; lean_object* v_tail_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4917_; 
v_head_4905_ = lean_ctor_get(v_a_4902_, 0);
v_tail_4906_ = lean_ctor_get(v_a_4902_, 1);
v_isSharedCheck_4917_ = !lean_is_exclusive(v_a_4902_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4908_ = v_a_4902_;
v_isShared_4909_ = v_isSharedCheck_4917_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_tail_4906_);
lean_inc(v_head_4905_);
lean_dec(v_a_4902_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4917_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4914_; 
v___x_4910_ = l_Nat_reprFast(v_head_4905_);
v___x_4911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
v___x_4912_ = l_Lean_MessageData_ofFormat(v___x_4911_);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 1, v_a_4903_);
lean_ctor_set(v___x_4908_, 0, v___x_4912_);
v___x_4914_ = v___x_4908_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4912_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v_a_4903_);
v___x_4914_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
v_a_4902_ = v_tail_4906_;
v_a_4903_ = v___x_4914_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4918_, lean_object* v_a_4919_){
_start:
{
if (lean_obj_tag(v_a_4918_) == 0)
{
lean_object* v___x_4920_; 
v___x_4920_ = l_List_reverse___redArg(v_a_4919_);
return v___x_4920_;
}
else
{
lean_object* v_head_4921_; lean_object* v_tail_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4934_; 
v_head_4921_ = lean_ctor_get(v_a_4918_, 0);
v_tail_4922_ = lean_ctor_get(v_a_4918_, 1);
v_isSharedCheck_4934_ = !lean_is_exclusive(v_a_4918_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4924_ = v_a_4918_;
v_isShared_4925_ = v_isSharedCheck_4934_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_tail_4922_);
lean_inc(v_head_4921_);
lean_dec(v_a_4918_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4934_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4931_; 
v___x_4926_ = lean_array_to_list(v_head_4921_);
v___x_4927_ = lean_box(0);
v___x_4928_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4926_, v___x_4927_);
v___x_4929_ = l_Lean_MessageData_ofList(v___x_4928_);
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 1, v_a_4919_);
lean_ctor_set(v___x_4924_, 0, v___x_4929_);
v___x_4931_ = v___x_4924_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4929_);
lean_ctor_set(v_reuseFailAlloc_4933_, 1, v_a_4919_);
v___x_4931_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
v_a_4918_ = v_tail_4922_;
v_a_4919_ = v___x_4931_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4935_, lean_object* v_v_4936_, lean_object* v_i_4937_){
_start:
{
lean_object* v___x_4938_; uint8_t v___x_4939_; 
v___x_4938_ = lean_array_get_size(v_xs_4935_);
v___x_4939_ = lean_nat_dec_lt(v_i_4937_, v___x_4938_);
if (v___x_4939_ == 0)
{
lean_object* v___x_4940_; 
lean_dec(v_i_4937_);
v___x_4940_ = lean_box(0);
return v___x_4940_;
}
else
{
lean_object* v___x_4941_; uint8_t v___x_4942_; 
v___x_4941_ = lean_array_fget_borrowed(v_xs_4935_, v_i_4937_);
v___x_4942_ = lean_nat_dec_eq(v___x_4941_, v_v_4936_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4943_ = lean_unsigned_to_nat(1u);
v___x_4944_ = lean_nat_add(v_i_4937_, v___x_4943_);
lean_dec(v_i_4937_);
v_i_4937_ = v___x_4944_;
goto _start;
}
else
{
lean_object* v___x_4946_; 
v___x_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4946_, 0, v_i_4937_);
return v___x_4946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4947_, lean_object* v_v_4948_, lean_object* v_i_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4947_, v_v_4948_, v_i_4949_);
lean_dec(v_v_4948_);
lean_dec_ref(v_xs_4947_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4951_, lean_object* v_v_4952_){
_start:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = lean_unsigned_to_nat(0u);
v___x_4954_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4951_, v_v_4952_, v___x_4953_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4955_, lean_object* v_v_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4955_, v_v_4956_);
lean_dec(v_v_4956_);
lean_dec_ref(v_xs_4955_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4961_, lean_object* v_as_4962_, size_t v_sz_4963_, size_t v_i_4964_, lean_object* v_b_4965_){
_start:
{
uint8_t v___x_4966_; 
v___x_4966_ = lean_usize_dec_lt(v_i_4964_, v_sz_4963_);
if (v___x_4966_ == 0)
{
lean_inc_ref(v_b_4965_);
return v_b_4965_;
}
else
{
lean_object* v___x_4967_; lean_object* v_a_4968_; lean_object* v___x_4969_; 
v___x_4967_ = lean_box(0);
v_a_4968_ = lean_array_uget_borrowed(v_as_4962_, v_i_4964_);
v___x_4969_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4968_, v_fnIdx_4961_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v___x_4970_; size_t v___x_4971_; size_t v___x_4972_; 
v___x_4970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4971_ = ((size_t)1ULL);
v___x_4972_ = lean_usize_add(v_i_4964_, v___x_4971_);
v_i_4964_ = v___x_4972_;
v_b_4965_ = v___x_4970_;
goto _start;
}
else
{
lean_object* v_val_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4985_; 
v_val_4974_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4976_ = v___x_4969_;
v_isShared_4977_ = v_isSharedCheck_4985_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_val_4974_);
lean_dec(v___x_4969_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4985_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4981_; 
v___x_4978_ = lean_array_get_size(v_a_4968_);
v___x_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
lean_ctor_set(v___x_4979_, 1, v_val_4974_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v___x_4979_);
v___x_4981_ = v___x_4976_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v___x_4979_);
v___x_4981_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4981_);
v___x_4983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
lean_ctor_set(v___x_4983_, 1, v___x_4967_);
return v___x_4983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4986_, lean_object* v_as_4987_, lean_object* v_sz_4988_, lean_object* v_i_4989_, lean_object* v_b_4990_){
_start:
{
size_t v_sz_boxed_4991_; size_t v_i_boxed_4992_; lean_object* v_res_4993_; 
v_sz_boxed_4991_ = lean_unbox_usize(v_sz_4988_);
lean_dec(v_sz_4988_);
v_i_boxed_4992_ = lean_unbox_usize(v_i_4989_);
lean_dec(v_i_4989_);
v_res_4993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4986_, v_as_4987_, v_sz_boxed_4991_, v_i_boxed_4992_, v_b_4990_);
lean_dec_ref(v_b_4990_);
lean_dec_ref(v_as_4987_);
lean_dec(v_fnIdx_4986_);
return v_res_4993_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4995_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4996_ = l_Lean_stringToMessageData(v___x_4995_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4997_, lean_object* v_positions_4998_, lean_object* v_fnIdx_4999_, lean_object* v_brecOnConst_5000_, lean_object* v_packedFArgs_5001_, lean_object* v_funTypes_5002_, lean_object* v_ys_5003_, lean_object* v___value_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
lean_object* v___y_5011_; lean_object* v___y_5012_; lean_object* v___y_5013_; lean_object* v___y_5014_; lean_object* v___x_5028_; lean_object* v_fst_5029_; lean_object* v_snd_5030_; lean_object* v___x_5031_; size_t v_sz_5032_; size_t v___x_5033_; lean_object* v___x_5034_; lean_object* v_fst_5035_; 
lean_inc_ref(v_ys_5003_);
lean_inc_ref(v_recArgInfo_4997_);
v___x_5028_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4997_, v_ys_5003_);
v_fst_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_fst_5029_);
v_snd_5030_ = lean_ctor_get(v___x_5028_, 1);
lean_inc(v_snd_5030_);
lean_dec_ref(v___x_5028_);
v___x_5031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5032_ = lean_array_size(v_positions_4998_);
v___x_5033_ = ((size_t)0ULL);
v___x_5034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4999_, v_positions_4998_, v_sz_5032_, v___x_5033_, v___x_5031_);
v_fst_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_fst_5035_);
lean_dec_ref(v___x_5034_);
if (lean_obj_tag(v_fst_5035_) == 0)
{
lean_dec(v_snd_5030_);
lean_dec(v_fst_5029_);
lean_dec_ref(v_ys_5003_);
lean_dec_ref(v_brecOnConst_5000_);
lean_dec_ref(v_recArgInfo_4997_);
v___y_5011_ = v___y_5005_;
v___y_5012_ = v___y_5006_;
v___y_5013_ = v___y_5007_;
v___y_5014_ = v___y_5008_;
goto v___jp_5010_;
}
else
{
lean_object* v_val_5036_; 
v_val_5036_ = lean_ctor_get(v_fst_5035_, 0);
lean_inc(v_val_5036_);
lean_dec_ref_known(v_fst_5035_, 1);
if (lean_obj_tag(v_val_5036_) == 1)
{
lean_object* v_val_5037_; lean_object* v_fst_5038_; lean_object* v_snd_5039_; lean_object* v_indIdx_5040_; lean_object* v_brecOn_5041_; lean_object* v_brecOn_5042_; lean_object* v_brecOn_5043_; lean_object* v___x_5044_; 
lean_dec(v_fnIdx_4999_);
lean_dec_ref(v_positions_4998_);
v_val_5037_ = lean_ctor_get(v_val_5036_, 0);
lean_inc(v_val_5037_);
lean_dec_ref_known(v_val_5036_, 1);
v_fst_5038_ = lean_ctor_get(v_val_5037_, 0);
lean_inc(v_fst_5038_);
v_snd_5039_ = lean_ctor_get(v_val_5037_, 1);
lean_inc(v_snd_5039_);
lean_dec(v_val_5037_);
v_indIdx_5040_ = lean_ctor_get(v_recArgInfo_4997_, 5);
lean_inc(v_indIdx_5040_);
lean_dec_ref(v_recArgInfo_4997_);
v_brecOn_5041_ = lean_apply_1(v_brecOnConst_5000_, v_indIdx_5040_);
v_brecOn_5042_ = l_Lean_mkAppN(v_brecOn_5041_, v_fst_5029_);
lean_dec(v_fst_5029_);
v_brecOn_5043_ = l_Lean_mkAppN(v_brecOn_5042_, v_packedFArgs_5001_);
v___x_5044_ = l_Lean_Meta_PProdN_projM(v_fst_5038_, v_snd_5039_, v_brecOn_5043_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
lean_dec(v_snd_5039_);
lean_dec(v_fst_5038_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; uint8_t v___x_5048_; lean_object* v___x_5049_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref_known(v___x_5044_, 1);
v___x_5046_ = l_Lean_mkAppN(v_a_5045_, v_snd_5030_);
lean_dec(v_snd_5030_);
v___x_5047_ = 1;
v___x_5048_ = 1;
v___x_5049_ = l_Lean_Meta_mkLetFVars(v_funTypes_5002_, v___x_5046_, v___x_5047_, v___x_5047_, v___x_5048_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; uint8_t v___x_5051_; lean_object* v___x_5052_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref_known(v___x_5049_, 1);
v___x_5051_ = 0;
v___x_5052_ = l_Lean_Meta_mkLambdaFVars(v_ys_5003_, v_a_5050_, v___x_5051_, v___x_5047_, v___x_5051_, v___x_5047_, v___x_5048_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
lean_dec_ref(v_ys_5003_);
return v___x_5052_;
}
else
{
lean_dec_ref(v_ys_5003_);
return v___x_5049_;
}
}
else
{
lean_dec(v_snd_5030_);
lean_dec_ref(v_ys_5003_);
return v___x_5044_;
}
}
else
{
lean_dec(v_val_5036_);
lean_dec(v_snd_5030_);
lean_dec(v_fst_5029_);
lean_dec_ref(v_ys_5003_);
lean_dec_ref(v_brecOnConst_5000_);
lean_dec_ref(v_recArgInfo_4997_);
v___y_5011_ = v___y_5005_;
v___y_5012_ = v___y_5006_;
v___y_5013_ = v___y_5007_;
v___y_5014_ = v___y_5008_;
goto v___jp_5010_;
}
}
v___jp_5010_:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5015_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_5016_ = l_Nat_reprFast(v_fnIdx_4999_);
v___x_5017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
v___x_5018_ = l_Lean_MessageData_ofFormat(v___x_5017_);
v___x_5019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5015_);
lean_ctor_set(v___x_5019_, 1, v___x_5018_);
v___x_5020_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_5021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5019_);
lean_ctor_set(v___x_5021_, 1, v___x_5020_);
v___x_5022_ = lean_array_to_list(v_positions_4998_);
v___x_5023_ = lean_box(0);
v___x_5024_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5022_, v___x_5023_);
v___x_5025_ = l_Lean_MessageData_ofList(v___x_5024_);
v___x_5026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5021_);
lean_ctor_set(v___x_5026_, 1, v___x_5025_);
v___x_5027_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5026_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
return v___x_5027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5053_, lean_object* v_positions_5054_, lean_object* v_fnIdx_5055_, lean_object* v_brecOnConst_5056_, lean_object* v_packedFArgs_5057_, lean_object* v_funTypes_5058_, lean_object* v_ys_5059_, lean_object* v___value_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5053_, v_positions_5054_, v_fnIdx_5055_, v_brecOnConst_5056_, v_packedFArgs_5057_, v_funTypes_5058_, v_ys_5059_, v___value_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
lean_dec(v___y_5062_);
lean_dec_ref(v___y_5061_);
lean_dec_ref(v___value_5060_);
lean_dec_ref(v_funTypes_5058_);
lean_dec_ref(v_packedFArgs_5057_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5067_, lean_object* v_fnIdx_5068_, lean_object* v_brecOnConst_5069_, lean_object* v_packedFArgs_5070_, lean_object* v_funTypes_5071_, lean_object* v_recArgInfo_5072_, lean_object* v_value_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v___f_5079_; uint8_t v___x_5080_; lean_object* v___x_5081_; 
v___f_5079_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5079_, 0, v_recArgInfo_5072_);
lean_closure_set(v___f_5079_, 1, v_positions_5067_);
lean_closure_set(v___f_5079_, 2, v_fnIdx_5068_);
lean_closure_set(v___f_5079_, 3, v_brecOnConst_5069_);
lean_closure_set(v___f_5079_, 4, v_packedFArgs_5070_);
lean_closure_set(v___f_5079_, 5, v_funTypes_5071_);
v___x_5080_ = 0;
v___x_5081_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5073_, v___f_5079_, v___x_5080_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5082_, lean_object* v_fnIdx_5083_, lean_object* v_brecOnConst_5084_, lean_object* v_packedFArgs_5085_, lean_object* v_funTypes_5086_, lean_object* v_recArgInfo_5087_, lean_object* v_value_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5082_, v_fnIdx_5083_, v_brecOnConst_5084_, v_packedFArgs_5085_, v_funTypes_5086_, v_recArgInfo_5087_, v_value_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
lean_dec(v_a_5092_);
lean_dec_ref(v_a_5091_);
lean_dec(v_a_5090_);
lean_dec_ref(v_a_5089_);
return v_res_5094_;
}
}
lean_object* runtime_initialize_Lean_Util_HasConstCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_BRecOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_HasConstCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Structural_BRecOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_HasConstCache(uint8_t builtin);
lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_BRecOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_HasConstCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin);
}
#ifdef __cplusplus
}
#endif
