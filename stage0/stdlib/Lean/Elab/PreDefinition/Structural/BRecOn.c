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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_withAppAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
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
lean_object* l_Lean_Meta_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "belowDict not an app:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "belowDict step 2:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "belowDict step 1:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "belowDict start:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\narg:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "C"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 87, 66, 208, 34, 24, 101, 135)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_PProdN_packLambdas___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not type correct!"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "initial belowDict for "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "numMotives: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unexpected 'below' type"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object**);
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
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "belowType: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17;
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_toBelow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Structural_toBelow___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "insufficient number of parameters at recursive application "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "failed to eliminate recursive application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0_value;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "unexpected matcher application alternative"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__0 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__0_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\nat application"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__2 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__2_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "altNumParams: "};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__4 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__4_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", xs: "};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__6 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__6_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_mkBRecOnConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_mkBRecOnConst___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_mkBRecOnConst___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_mkBRecOnConst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_109_);
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
lean_dec_ref(v_a_110_);
v_arg_116_ = lean_ctor_get(v_fn_111_, 1);
lean_inc_ref(v_arg_116_);
lean_dec_ref(v_fn_111_);
v_str_117_ = lean_ctor_get(v_declName_113_, 1);
lean_inc_ref(v_str_117_);
lean_dec_ref(v_declName_113_);
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
lean_dec_ref(v___x_123_);
v___x_125_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__2));
v___x_126_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_102_);
v___x_127_ = l_Lean_Expr_proj___override(v___x_125_, v___x_126_, v_F_102_);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
lean_inc_ref(v_k_103_);
v___x_128_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_116_, v___x_127_, v_k_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_dec(v_a_124_);
lean_dec_ref(v_arg_115_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec_ref(v___x_128_);
v___x_132_ = l_Lean_Meta_SavedState_restore___redArg(v_a_124_, v_a_105_, v_a_107_);
lean_dec(v_a_124_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec_ref(v___x_132_);
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
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec_ref(v___x_154_);
v___x_156_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__3));
v___x_157_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_102_);
v___x_158_ = l_Lean_Expr_proj___override(v___x_156_, v___x_157_, v_F_102_);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
lean_inc_ref(v_k_103_);
v___x_159_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_116_, v___x_158_, v_k_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_dec(v_a_155_);
lean_dec_ref(v_arg_115_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec_ref(v___x_159_);
v___x_163_ = l_Lean_Meta_SavedState_restore___redArg(v_a_155_, v_a_105_, v_a_107_);
lean_dec(v_a_155_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec_ref(v___x_163_);
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
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec_ref(v_declName_113_);
lean_dec_ref(v_fn_111_);
lean_dec_ref(v_a_110_);
v___x_185_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_185_;
}
}
else
{
lean_object* v___x_186_; 
lean_dec(v_declName_113_);
lean_dec_ref(v_fn_111_);
lean_dec_ref(v_a_110_);
v___x_186_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_186_;
}
}
else
{
lean_object* v___x_187_; 
lean_dec_ref(v_fn_111_);
lean_dec_ref(v_a_110_);
v___x_187_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_187_;
}
}
else
{
lean_object* v___x_188_; 
lean_dec_ref(v_a_110_);
lean_dec_ref(v_fn_111_);
v___x_188_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_188_;
}
}
case 4:
{
lean_object* v_declName_189_; 
v_declName_189_ = lean_ctor_get(v_a_110_, 0);
lean_inc(v_declName_189_);
lean_dec_ref(v_a_110_);
if (lean_obj_tag(v_declName_189_) == 1)
{
lean_object* v_pre_190_; 
v_pre_190_ = lean_ctor_get(v_declName_189_, 0);
if (lean_obj_tag(v_pre_190_) == 0)
{
lean_object* v_str_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_str_191_ = lean_ctor_get(v_declName_189_, 1);
lean_inc_ref(v_str_191_);
lean_dec_ref(v_declName_189_);
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
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec_ref(v_declName_189_);
v___x_199_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_199_;
}
}
else
{
lean_object* v___x_200_; 
lean_dec(v_declName_189_);
v___x_200_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_200_;
}
}
default: 
{
lean_object* v___x_201_; 
lean_dec(v_a_110_);
v___x_201_ = lean_apply_7(v_k_103_, v_e_101_, v_F_102_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, lean_box(0));
return v___x_201_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
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
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(lean_object* v_cls_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_options_245_; uint8_t v_hasTrace_246_; 
v_options_245_ = lean_ctor_get(v___y_243_, 2);
v_hasTrace_246_ = lean_ctor_get_uint8(v_options_245_, sizeof(void*)*1);
if (v_hasTrace_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_cls_242_);
v___x_247_ = lean_box(v_hasTrace_246_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
else
{
lean_object* v_inheritedTraceOptions_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_inheritedTraceOptions_249_ = lean_ctor_get(v___y_243_, 13);
v___x_250_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__1));
v___x_251_ = l_Lean_Name_append(v___x_250_, v_cls_242_);
v___x_252_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_249_, v_options_245_, v___x_251_);
lean_dec(v___x_251_);
v___x_253_ = lean_box(v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___boxed(lean_object* v_cls_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(v_cls_255_, v___y_256_);
lean_dec_ref(v___y_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(lean_object* v_cls_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(v_cls_259_, v___y_262_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object* v_cls_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0(lean_object* v_k_273_, lean_object* v_b_274_, lean_object* v_c_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_apply_7(v_k_273_, v_b_274_, v_c_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, lean_box(0));
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0___boxed(lean_object* v_k_282_, lean_object* v_b_283_, lean_object* v_c_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0(v_k_282_, v_b_283_, v_c_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg(lean_object* v_type_291_, lean_object* v_k_292_, uint8_t v_cleanupAnnotations_293_, uint8_t v_whnfType_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; 
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_300_, 0, v_k_292_);
v___x_301_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_291_, v___f_300_, v_cleanupAnnotations_293_, v_whnfType_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_310_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_301_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_301_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___boxed(lean_object* v_type_318_, lean_object* v_k_319_, lean_object* v_cleanupAnnotations_320_, lean_object* v_whnfType_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_327_; uint8_t v_whnfType_boxed_328_; lean_object* v_res_329_; 
v_cleanupAnnotations_boxed_327_ = lean_unbox(v_cleanupAnnotations_320_);
v_whnfType_boxed_328_ = lean_unbox(v_whnfType_321_);
v_res_329_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg(v_type_318_, v_k_319_, v_cleanupAnnotations_boxed_327_, v_whnfType_boxed_328_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2(lean_object* v_00_u03b1_330_, lean_object* v_type_331_, lean_object* v_k_332_, uint8_t v_cleanupAnnotations_333_, uint8_t v_whnfType_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg(v_type_331_, v_k_332_, v_cleanupAnnotations_333_, v_whnfType_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___boxed(lean_object* v_00_u03b1_341_, lean_object* v_type_342_, lean_object* v_k_343_, lean_object* v_cleanupAnnotations_344_, lean_object* v_whnfType_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_351_; uint8_t v_whnfType_boxed_352_; lean_object* v_res_353_; 
v_cleanupAnnotations_boxed_351_ = lean_unbox(v_cleanupAnnotations_344_);
v_whnfType_boxed_352_ = lean_unbox(v_whnfType_345_);
v_res_353_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2(v_00_u03b1_341_, v_type_342_, v_k_343_, v_cleanupAnnotations_boxed_351_, v_whnfType_boxed_352_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
return v_res_353_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0(void){
_start:
{
lean_object* v___x_354_; double v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_float_of_nat(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_object* v_cls_359_, lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_ref_366_; lean_object* v___x_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_412_; 
v_ref_366_ = lean_ctor_get(v___y_363_, 5);
v___x_367_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_412_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_412_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_412_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v_traceState_373_; lean_object* v_env_374_; lean_object* v_nextMacroScope_375_; lean_object* v_ngen_376_; lean_object* v_auxDeclNGen_377_; lean_object* v_cache_378_; lean_object* v_messages_379_; lean_object* v_infoState_380_; lean_object* v_snapshotTasks_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_411_; 
v___x_372_ = lean_st_ref_take(v___y_364_);
v_traceState_373_ = lean_ctor_get(v___x_372_, 4);
v_env_374_ = lean_ctor_get(v___x_372_, 0);
v_nextMacroScope_375_ = lean_ctor_get(v___x_372_, 1);
v_ngen_376_ = lean_ctor_get(v___x_372_, 2);
v_auxDeclNGen_377_ = lean_ctor_get(v___x_372_, 3);
v_cache_378_ = lean_ctor_get(v___x_372_, 5);
v_messages_379_ = lean_ctor_get(v___x_372_, 6);
v_infoState_380_ = lean_ctor_get(v___x_372_, 7);
v_snapshotTasks_381_ = lean_ctor_get(v___x_372_, 8);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_411_ == 0)
{
v___x_383_ = v___x_372_;
v_isShared_384_ = v_isSharedCheck_411_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snapshotTasks_381_);
lean_inc(v_infoState_380_);
lean_inc(v_messages_379_);
lean_inc(v_cache_378_);
lean_inc(v_traceState_373_);
lean_inc(v_auxDeclNGen_377_);
lean_inc(v_ngen_376_);
lean_inc(v_nextMacroScope_375_);
lean_inc(v_env_374_);
lean_dec(v___x_372_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_411_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint64_t v_tid_385_; lean_object* v_traces_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_410_; 
v_tid_385_ = lean_ctor_get_uint64(v_traceState_373_, sizeof(void*)*1);
v_traces_386_ = lean_ctor_get(v_traceState_373_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_traceState_373_);
if (v_isSharedCheck_410_ == 0)
{
v___x_388_ = v_traceState_373_;
v_isShared_389_ = v_isSharedCheck_410_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_traces_386_);
lean_dec(v_traceState_373_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_410_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; double v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_390_ = lean_box(0);
v___x_391_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0);
v___x_392_ = 0;
v___x_393_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__1));
v___x_394_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_394_, 0, v_cls_359_);
lean_ctor_set(v___x_394_, 1, v___x_390_);
lean_ctor_set(v___x_394_, 2, v___x_393_);
lean_ctor_set_float(v___x_394_, sizeof(void*)*3, v___x_391_);
lean_ctor_set_float(v___x_394_, sizeof(void*)*3 + 8, v___x_391_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*3 + 16, v___x_392_);
v___x_395_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__2));
v___x_396_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v_a_368_);
lean_ctor_set(v___x_396_, 2, v___x_395_);
lean_inc(v_ref_366_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_ref_366_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_PersistentArray_push___redArg(v_traces_386_, v___x_397_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_398_);
v___x_400_ = v___x_388_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_398_);
lean_ctor_set_uint64(v_reuseFailAlloc_409_, sizeof(void*)*1, v_tid_385_);
v___x_400_ = v_reuseFailAlloc_409_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 4, v___x_400_);
v___x_402_ = v___x_383_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_env_374_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_nextMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_ngen_376_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_auxDeclNGen_377_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_cache_378_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_messages_379_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_infoState_380_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_snapshotTasks_381_);
v___x_402_ = v_reuseFailAlloc_408_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = lean_st_ref_set(v___y_364_, v___x_402_);
v___x_404_ = lean_box(0);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_404_);
v___x_406_ = v___x_370_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___boxed(lean_object* v_cls_413_, lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_cls_413_, v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__0));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__3(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__2));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(lean_object* v_cls_427_, lean_object* v_a_428_, lean_object* v_C_429_, lean_object* v_belowDict_430_, lean_object* v_F_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___x_505_; lean_object* v_a_506_; uint8_t v___x_507_; 
lean_inc(v_cls_427_);
v___x_505_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(v_cls_427_, v___y_434_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
v___x_507_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
if (v___x_507_ == 0)
{
v___y_471_ = v___y_432_;
v___y_472_ = v___y_433_;
v___y_473_ = v___y_434_;
v___y_474_ = v___y_435_;
goto v___jp_470_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_508_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__3);
lean_inc_ref(v_belowDict_430_);
v___x_509_ = l_Lean_indentExpr(v_belowDict_430_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
lean_inc(v_cls_427_);
v___x_511_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_cls_427_, v___x_510_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_dec_ref(v___x_511_);
v___y_471_ = v___y_432_;
v___y_472_ = v___y_433_;
v___y_473_ = v___y_434_;
v___y_474_ = v___y_435_;
goto v___jp_470_;
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec_ref(v_F_431_);
lean_dec_ref(v_belowDict_430_);
lean_dec_ref(v_a_428_);
lean_dec(v_cls_427_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
v___jp_437_:
{
lean_object* v___x_443_; 
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
v___x_443_ = l_Lean_Meta_isExprDefEq(v___y_438_, v_a_428_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_461_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_461_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_461_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_461_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; 
v___x_448_ = lean_unbox(v_a_444_);
lean_dec(v_a_444_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_del_object(v___x_446_);
lean_dec_ref(v_F_431_);
v___x_449_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_F_431_);
v___x_459_ = v___x_446_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_F_431_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec_ref(v_F_431_);
v_a_462_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_443_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_443_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
v___jp_470_:
{
if (lean_obj_tag(v_belowDict_430_) == 5)
{
lean_object* v_fn_475_; lean_object* v_arg_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
lean_dec(v_cls_427_);
v_fn_475_ = lean_ctor_get(v_belowDict_430_, 0);
lean_inc_ref(v_fn_475_);
v_arg_476_ = lean_ctor_get(v_belowDict_430_, 1);
lean_inc_ref(v_arg_476_);
lean_dec_ref(v_belowDict_430_);
v___x_477_ = l_Lean_Expr_getAppFn(v_fn_475_);
lean_dec_ref(v_fn_475_);
v___x_478_ = lean_expr_eqv(v___x_477_, v_C_429_);
lean_dec_ref(v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v_arg_476_);
lean_dec_ref(v_F_431_);
lean_dec_ref(v_a_428_);
v___x_479_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
v___y_438_ = v_arg_476_;
v___y_439_ = v___y_471_;
v___y_440_ = v___y_472_;
v___y_441_ = v___y_473_;
v___y_442_ = v___y_474_;
goto v___jp_437_;
}
}
else
{
lean_object* v___x_488_; lean_object* v_a_489_; uint8_t v___x_490_; 
lean_dec_ref(v_F_431_);
lean_dec_ref(v_a_428_);
lean_inc(v_cls_427_);
v___x_488_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(v_cls_427_, v___y_473_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
v___x_490_ = lean_unbox(v_a_489_);
lean_dec(v_a_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec_ref(v_belowDict_430_);
lean_dec(v_cls_427_);
v___x_491_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_492_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1);
v___x_493_ = l_Lean_indentExpr(v_belowDict_430_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_cls_427_, v___x_494_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_496_; 
lean_dec_ref(v___x_495_);
v___x_496_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v___x_496_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
v_a_497_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_495_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_495_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed(lean_object* v_cls_520_, lean_object* v_a_521_, lean_object* v_C_522_, lean_object* v_belowDict_523_, lean_object* v_F_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_520_, v_a_521_, v_C_522_, v_belowDict_523_, v_F_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec_ref(v_C_522_);
return v_res_530_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0(void){
_start:
{
lean_object* v___x_531_; lean_object* v_dummy_532_; 
v___x_531_ = lean_box(0);
v_dummy_532_ = l_Lean_Expr_sort___override(v___x_531_);
return v_dummy_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v_arg_533_, lean_object* v_cls_534_, lean_object* v_C_535_, lean_object* v_F_536_, lean_object* v_xs_537_, lean_object* v_belowDict_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
uint8_t v___x_544_; lean_object* v___x_545_; 
v___x_544_ = 1;
lean_inc(v___y_542_);
lean_inc_ref(v___y_541_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
v___x_545_ = l_Lean_Meta_zetaReduce(v_arg_533_, v___x_544_, v___x_544_, v___x_544_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___f_547_; lean_object* v_dummy_548_; lean_object* v_nargs_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
lean_inc(v_a_546_);
v___f_547_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed), 10, 3);
lean_closure_set(v___f_547_, 0, v_cls_534_);
lean_closure_set(v___f_547_, 1, v_a_546_);
lean_closure_set(v___f_547_, 2, v_C_535_);
v_dummy_548_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
v_nargs_549_ = l_Lean_Expr_getAppNumArgs(v_a_546_);
lean_inc(v_nargs_549_);
v___x_550_ = lean_mk_array(v_nargs_549_, v_dummy_548_);
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_sub(v_nargs_549_, v___x_551_);
lean_dec(v_nargs_549_);
v___x_553_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_546_, v___x_550_, v___x_552_);
v___x_566_ = lean_array_get_size(v_xs_537_);
v___x_567_ = lean_array_get_size(v___x_553_);
v___x_568_ = lean_nat_dec_le(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v___x_553_);
lean_dec_ref(v___f_547_);
lean_dec_ref(v_F_536_);
v___x_569_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
v___y_555_ = v___y_539_;
v___y_556_ = v___y_540_;
v___y_557_ = v___y_541_;
v___y_558_ = v___y_542_;
goto v___jp_554_;
}
v___jp_554_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_559_ = lean_array_get_size(v___x_553_);
v___x_560_ = lean_array_get_size(v_xs_537_);
v___x_561_ = lean_nat_sub(v___x_559_, v___x_560_);
v___x_562_ = l_Array_extract___redArg(v___x_553_, v___x_561_, v___x_559_);
lean_dec_ref(v___x_553_);
v___x_563_ = l_Lean_Expr_replaceFVars(v_belowDict_538_, v_xs_537_, v___x_562_);
v___x_564_ = l_Lean_mkAppN(v_F_536_, v___x_562_);
lean_dec_ref(v___x_562_);
v___x_565_ = l_Lean_Elab_Structural_searchPProd___redArg(v___x_563_, v___x_564_, v___f_547_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
return v___x_565_;
}
}
else
{
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v_F_536_);
lean_dec_ref(v_C_535_);
lean_dec(v_cls_534_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v_arg_578_, lean_object* v_cls_579_, lean_object* v_C_580_, lean_object* v_F_581_, lean_object* v_xs_582_, lean_object* v_belowDict_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v_arg_578_, v_cls_579_, v_C_580_, v_F_581_, v_xs_582_, v_belowDict_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec_ref(v_belowDict_583_);
lean_dec_ref(v_xs_582_);
return v_res_589_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__1(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0));
v___x_592_ = l_Lean_stringToMessageData(v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_cls_593_, lean_object* v_arg_594_, lean_object* v_C_595_, lean_object* v_belowDict_596_, lean_object* v_F_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; lean_object* v_a_604_; lean_object* v___f_605_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; uint8_t v___x_613_; 
lean_inc(v_cls_593_);
v___x_603_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(v_cls_593_, v___y_600_);
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref(v___x_603_);
lean_inc(v_cls_593_);
v___f_605_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed), 11, 4);
lean_closure_set(v___f_605_, 0, v_arg_594_);
lean_closure_set(v___f_605_, 1, v_cls_593_);
lean_closure_set(v___f_605_, 2, v_C_595_);
lean_closure_set(v___f_605_, 3, v_F_597_);
v___x_613_ = lean_unbox(v_a_604_);
lean_dec(v_a_604_);
if (v___x_613_ == 0)
{
lean_dec(v_cls_593_);
v___y_607_ = v___y_598_;
v___y_608_ = v___y_599_;
v___y_609_ = v___y_600_;
v___y_610_ = v___y_601_;
goto v___jp_606_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__1);
lean_inc_ref(v_belowDict_596_);
v___x_615_ = l_Lean_indentExpr(v_belowDict_596_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_cls_593_, v___x_616_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_dec_ref(v___x_617_);
v___y_607_ = v___y_598_;
v___y_608_ = v___y_599_;
v___y_609_ = v___y_600_;
v___y_610_ = v___y_601_;
goto v___jp_606_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v___f_605_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec_ref(v_belowDict_596_);
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
v___jp_606_:
{
uint8_t v___x_611_; lean_object* v___x_612_; 
v___x_611_ = 0;
v___x_612_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg(v_belowDict_596_, v___f_605_, v___x_611_, v___x_611_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_cls_626_, lean_object* v_arg_627_, lean_object* v_C_628_, lean_object* v_belowDict_629_, lean_object* v_F_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_cls_626_, v_arg_627_, v_C_628_, v_belowDict_629_, v_F_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
return v_res_636_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_650_, lean_object* v_belowDict_651_, lean_object* v_arg_652_, lean_object* v_F_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_cls_659_; lean_object* v___x_660_; lean_object* v_a_661_; lean_object* v___f_662_; uint8_t v___x_663_; 
v_cls_659_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_660_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(v_cls_659_, v_a_656_);
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v___x_660_);
lean_inc_ref(v_arg_652_);
v___f_662_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 10, 3);
lean_closure_set(v___f_662_, 0, v_cls_659_);
lean_closure_set(v___f_662_, 1, v_arg_652_);
lean_closure_set(v___f_662_, 2, v_C_650_);
v___x_663_ = lean_unbox(v_a_661_);
lean_dec(v_a_661_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec_ref(v_arg_652_);
v___x_664_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_651_, v_F_653_, v___f_662_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_665_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5);
lean_inc_ref(v_belowDict_651_);
v___x_666_ = l_Lean_indentExpr(v_belowDict_651_);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_indentExpr(v_arg_652_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_cls_659_, v___x_671_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v___x_672_);
v___x_673_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_651_, v_F_653_, v___f_662_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
return v___x_673_;
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v___f_662_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec_ref(v_F_653_);
lean_dec_ref(v_belowDict_651_);
v_a_674_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_672_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_682_, lean_object* v_belowDict_683_, lean_object* v_arg_684_, lean_object* v_F_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_682_, v_belowDict_683_, v_arg_684_, v_F_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v_t_692_, lean_object* v_x_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v_t_692_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v_t_700_, lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v_t_700_, v_x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v_x_701_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1));
v___x_718_ = l_Lean_Core_mkFreshUserName(v___x_717_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_728_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_728_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_728_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_728_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___f_723_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_723_, 0, v_t_711_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v_a_719_);
lean_ctor_set(v___x_724_, 1, v___f_723_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_724_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_t_711_);
v_a_729_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_718_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_718_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v___x_744_, lean_object* v_a_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_array_set(v___y_747_, v_a_745_, v___x_744_);
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v___x_756_, lean_object* v_a_757_, lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v___x_756_, v_a_757_, v_x_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v_a_757_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_766_, lean_object* v_a_767_, lean_object* v_x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_snd_775_; lean_object* v_fst_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_827_; 
v_snd_775_ = lean_ctor_get(v___y_769_, 1);
v_fst_776_ = lean_ctor_get(v___y_769_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___y_769_);
if (v_isSharedCheck_827_ == 0)
{
v___x_778_ = v___y_769_;
v_isShared_779_ = v_isSharedCheck_827_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_775_);
lean_inc(v_fst_776_);
lean_dec(v___y_769_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_827_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_array_780_; lean_object* v_start_781_; lean_object* v_stop_782_; uint8_t v___x_783_; 
v_array_780_ = lean_ctor_get(v_snd_775_, 0);
v_start_781_ = lean_ctor_get(v_snd_775_, 1);
v_stop_782_ = lean_ctor_get(v_snd_775_, 2);
v___x_783_ = lean_nat_dec_lt(v_start_781_, v_stop_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec_ref(v_a_767_);
lean_dec_ref(v___x_766_);
if (v_isShared_779_ == 0)
{
v___x_785_ = v___x_778_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_fst_776_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_snd_775_);
v___x_785_ = v_reuseFailAlloc_788_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
else
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_823_; 
lean_inc(v_stop_782_);
lean_inc(v_start_781_);
lean_inc_ref(v_array_780_);
v_isSharedCheck_823_ = !lean_is_exclusive(v_snd_775_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; 
v_unused_824_ = lean_ctor_get(v_snd_775_, 2);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_snd_775_, 1);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_snd_775_, 0);
lean_dec(v_unused_826_);
v___x_790_ = v_snd_775_;
v_isShared_791_ = v_isSharedCheck_823_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_snd_775_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_823_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___f_793_; size_t v_sz_794_; size_t v___x_795_; lean_object* v___x_8044__overap_796_; lean_object* v___x_797_; 
v___x_792_ = lean_array_fget_borrowed(v_array_780_, v_start_781_);
lean_inc(v___x_792_);
v___f_793_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_793_, 0, v___x_792_);
v_sz_794_ = lean_array_size(v_a_767_);
v___x_795_ = ((size_t)0ULL);
v___x_8044__overap_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_766_, v_a_767_, v___f_793_, v_sz_794_, v___x_795_, v_fst_776_);
v___x_797_ = lean_apply_5(v___x_8044__overap_796_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, lean_box(0));
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_814_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_814_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_814_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_814_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_add(v_start_781_, v___x_802_);
lean_dec(v_start_781_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v___x_803_);
v___x_805_ = v___x_790_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_array_780_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_stop_782_);
v___x_805_ = v_reuseFailAlloc_813_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v___x_805_);
lean_ctor_set(v___x_778_, 0, v_a_798_);
v___x_807_ = v___x_778_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_798_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_812_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_808_);
v___x_810_ = v___x_800_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_del_object(v___x_790_);
lean_dec(v_stop_782_);
lean_dec(v_start_781_);
lean_dec_ref(v_array_780_);
lean_del_object(v___x_778_);
v_a_815_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_797_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_797_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_828_, lean_object* v_a_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_828_, v_a_829_, v_x_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
return v_res_837_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__7));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v_positions_852_, lean_object* v_a_853_, lean_object* v___x_854_, lean_object* v___x_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v___x_858_, lean_object* v_k_859_, lean_object* v___x_860_, lean_object* v___f_861_, lean_object* v_Cs_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_8072__overap_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__0));
lean_inc_ref(v_Cs_862_);
lean_inc_ref(v___x_850_);
v___x_8072__overap_869_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_850_, v___x_851_, v___x_868_, v_positions_852_, v_a_853_, v_Cs_862_);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
v___x_870_ = lean_apply_5(v___x_8072__overap_869_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, lean_box(0));
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_8075__overap_872_; lean_object* v___x_873_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v___x_870_);
lean_inc(v___x_856_);
lean_inc(v___x_855_);
lean_inc_ref(v___x_854_);
lean_inc_ref(v___x_850_);
v___x_8075__overap_872_ = l_Lean_isTracingEnabledFor___redArg(v___x_850_, v___x_854_, v___x_855_, v___x_856_);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
v___x_873_ = lean_apply_5(v___x_8075__overap_872_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, lean_box(0));
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; uint8_t v___x_926_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = l_Lean_mkAppN(v___x_857_, v_a_871_);
lean_dec(v_a_871_);
v___x_876_ = l_Subarray_copy___redArg(v___x_858_);
v___x_877_ = l_Lean_mkAppN(v___x_875_, v___x_876_);
lean_dec_ref(v___x_876_);
v___x_926_ = lean_unbox(v_a_874_);
lean_dec(v_a_874_);
if (v___x_926_ == 0)
{
v___y_879_ = v___y_863_;
v___y_880_ = v___y_864_;
v___y_881_ = v___y_865_;
v___y_882_ = v___y_866_;
goto v___jp_878_;
}
else
{
lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_toMonadRef_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_8135__overap_944_; lean_object* v___x_945_; 
v___f_927_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_928_ = l_Lean_Core_instMonadQuotationCoreM;
lean_inc(v___x_860_);
v___x_929_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_927_, v___x_860_, v___x_928_);
lean_inc(v___f_861_);
v___x_930_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_927_, v___f_861_, v___x_929_);
v_toMonadRef_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_toMonadRef_931_);
lean_dec_ref(v___x_930_);
v___x_932_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_933_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5);
lean_inc_ref(v_Cs_862_);
v___x_934_ = lean_array_to_list(v_Cs_862_);
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6));
v___x_936_ = lean_box(0);
v___x_937_ = l_List_mapTR_loop___redArg(v___x_935_, v___x_934_, v___x_936_);
v___x_938_ = l_Lean_MessageData_ofList(v___x_937_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_933_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
lean_inc_ref(v___x_877_);
v___x_942_ = l_Lean_indentExpr(v___x_877_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
lean_inc(v___x_856_);
lean_inc_ref(v___x_854_);
lean_inc_ref(v___x_850_);
v___x_8135__overap_944_ = l_Lean_addTrace___redArg(v___x_850_, v___x_854_, v_toMonadRef_931_, v___x_932_, v___x_856_, v___x_943_);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
v___x_945_ = lean_apply_5(v___x_8135__overap_944_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, lean_box(0));
if (lean_obj_tag(v___x_945_) == 0)
{
lean_dec_ref(v___x_945_);
v___y_879_ = v___y_863_;
v___y_880_ = v___y_864_;
v___y_881_ = v___y_865_;
v___y_882_ = v___y_866_;
goto v___jp_878_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v___x_877_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v_Cs_862_);
lean_dec(v___f_861_);
lean_dec(v___x_860_);
lean_dec_ref(v_k_859_);
lean_dec(v___x_856_);
lean_dec(v___x_855_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_850_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
v___jp_878_:
{
lean_object* v___x_883_; 
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc_ref(v___x_877_);
v___x_883_ = l_Lean_Meta_isTypeCorrect(v___x_877_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; uint8_t v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = lean_unbox(v_a_884_);
lean_dec(v_a_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_8090__overap_886_; lean_object* v___x_887_; 
lean_inc(v___x_856_);
lean_inc_ref(v___x_854_);
lean_inc_ref(v___x_850_);
v___x_8090__overap_886_ = l_Lean_isTracingEnabledFor___redArg(v___x_850_, v___x_854_, v___x_855_, v___x_856_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
v___x_887_ = lean_apply_5(v___x_8090__overap_886_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; uint8_t v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref(v___x_887_);
v___x_889_ = lean_unbox(v_a_888_);
lean_dec(v_a_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v___f_861_);
lean_dec(v___x_860_);
lean_dec(v___x_856_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_850_);
v___x_890_ = lean_apply_7(v_k_859_, v_Cs_862_, v___x_877_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
return v___x_890_;
}
else
{
lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_toMonadRef_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_8102__overap_898_; lean_object* v___x_899_; 
v___f_891_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_892_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_893_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_891_, v___x_860_, v___x_892_);
v___x_894_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_891_, v___f_861_, v___x_893_);
v_toMonadRef_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_toMonadRef_895_);
lean_dec_ref(v___x_894_);
v___x_896_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_897_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3);
v___x_8102__overap_898_ = l_Lean_addTrace___redArg(v___x_850_, v___x_854_, v_toMonadRef_895_, v___x_896_, v___x_856_, v___x_897_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
v___x_899_ = lean_apply_5(v___x_8102__overap_898_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; 
lean_dec_ref(v___x_899_);
v___x_900_ = lean_apply_7(v_k_859_, v_Cs_862_, v___x_877_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
return v___x_900_;
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v___x_877_);
lean_dec_ref(v_Cs_862_);
lean_dec_ref(v_k_859_);
v_a_901_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_899_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_899_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v___x_877_);
lean_dec_ref(v_Cs_862_);
lean_dec(v___f_861_);
lean_dec(v___x_860_);
lean_dec_ref(v_k_859_);
lean_dec(v___x_856_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_850_);
v_a_909_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_887_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_887_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v___x_917_; 
lean_dec(v___f_861_);
lean_dec(v___x_860_);
lean_dec(v___x_856_);
lean_dec(v___x_855_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_850_);
v___x_917_ = lean_apply_7(v_k_859_, v_Cs_862_, v___x_877_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
return v___x_917_;
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v___x_877_);
lean_dec_ref(v_Cs_862_);
lean_dec(v___f_861_);
lean_dec(v___x_860_);
lean_dec_ref(v_k_859_);
lean_dec(v___x_856_);
lean_dec(v___x_855_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_850_);
v_a_918_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_883_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_883_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_a_871_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v_Cs_862_);
lean_dec(v___f_861_);
lean_dec(v___x_860_);
lean_dec_ref(v_k_859_);
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_857_);
lean_dec(v___x_856_);
lean_dec(v___x_855_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_850_);
v_a_954_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_873_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_873_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v_Cs_862_);
lean_dec(v___f_861_);
lean_dec(v___x_860_);
lean_dec_ref(v_k_859_);
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_857_);
lean_dec(v___x_856_);
lean_dec(v___x_855_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_850_);
v_a_962_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_870_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_870_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_970_ = _args[0];
lean_object* v___x_971_ = _args[1];
lean_object* v_positions_972_ = _args[2];
lean_object* v_a_973_ = _args[3];
lean_object* v___x_974_ = _args[4];
lean_object* v___x_975_ = _args[5];
lean_object* v___x_976_ = _args[6];
lean_object* v___x_977_ = _args[7];
lean_object* v___x_978_ = _args[8];
lean_object* v_k_979_ = _args[9];
lean_object* v___x_980_ = _args[10];
lean_object* v___f_981_ = _args[11];
lean_object* v_Cs_982_ = _args[12];
lean_object* v___y_983_ = _args[13];
lean_object* v___y_984_ = _args[14];
lean_object* v___y_985_ = _args[15];
lean_object* v___y_986_ = _args[16];
lean_object* v___y_987_ = _args[17];
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_970_, v___x_971_, v_positions_972_, v_a_973_, v___x_974_, v___x_975_, v___x_976_, v___x_977_, v___x_978_, v_k_979_, v___x_980_, v___f_981_, v_Cs_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v_res_988_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_unsigned_to_nat(37u);
v___x_990_ = l_Lean_Level_ofNat(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0);
v___x_992_ = l_Lean_Expr_sort___override(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v_positions_999_, lean_object* v___x_1000_, lean_object* v___f_1001_, lean_object* v___f_1002_, lean_object* v___x_1003_, lean_object* v_numTypeFormers_1004_, lean_object* v___x_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v_k_1009_, lean_object* v___x_1010_, lean_object* v___f_1011_, lean_object* v_numIndParams_1012_, lean_object* v_a_1013_, lean_object* v_f_1014_, lean_object* v_args_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1154_ = lean_nat_add(v_numIndParams_1012_, v_numTypeFormers_1004_);
v___x_1155_ = lean_array_get_size(v_args_1015_);
v___x_1156_ = lean_nat_dec_lt(v___x_1154_, v___x_1155_);
lean_dec(v___x_1154_);
if (v___x_1156_ == 0)
{
lean_object* v___x_8255__overap_1157_; lean_object* v___x_1158_; 
lean_dec_ref(v_args_1015_);
lean_dec_ref(v_f_1014_);
lean_dec(v_numIndParams_1012_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v___x_1008_);
lean_dec(v_numTypeFormers_1004_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v_positions_999_);
lean_inc(v___x_1007_);
lean_inc_ref(v___x_1005_);
lean_inc_ref(v___x_1000_);
v___x_8255__overap_1157_ = l_Lean_isTracingEnabledFor___redArg(v___x_1000_, v___x_1005_, v___x_1006_, v___x_1007_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1158_ = lean_apply_5(v___x_8255__overap_1157_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, lean_box(0));
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; uint8_t v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref(v___x_1158_);
v___x_1160_ = lean_unbox(v_a_1159_);
lean_dec(v_a_1159_);
if (v___x_1160_ == 0)
{
lean_dec_ref(v_a_1013_);
lean_dec(v___f_1011_);
lean_dec(v___x_1010_);
lean_dec(v___x_1007_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v___x_1000_);
v___y_1141_ = v___y_1016_;
v___y_1142_ = v___y_1017_;
v___y_1143_ = v___y_1018_;
v___y_1144_ = v___y_1019_;
goto v___jp_1140_;
}
else
{
lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_toMonadRef_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_8280__overap_1170_; lean_object* v___x_1171_; 
v___f_1161_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_1162_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1163_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1161_, v___x_1010_, v___x_1162_);
v___x_1164_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1161_, v___f_1011_, v___x_1163_);
v_toMonadRef_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc_ref(v_toMonadRef_1165_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1167_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5);
v___x_1168_ = l_Lean_indentExpr(v_a_1013_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_8280__overap_1170_ = l_Lean_addTrace___redArg(v___x_1000_, v___x_1005_, v_toMonadRef_1165_, v___x_1166_, v___x_1007_, v___x_1169_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1171_ = lean_apply_5(v___x_8280__overap_1170_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, lean_box(0));
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_dec_ref(v___x_1171_);
v___y_1141_ = v___y_1016_;
v___y_1142_ = v___y_1017_;
v___y_1143_ = v___y_1018_;
v___y_1144_ = v___y_1019_;
goto v___jp_1140_;
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec_ref(v_a_1013_);
lean_dec(v___f_1011_);
lean_dec(v___x_1010_);
lean_dec(v___x_1007_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v___x_1000_);
v_a_1180_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1158_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1158_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_dec_ref(v_a_1013_);
v___y_1129_ = v___y_1016_;
v___y_1130_ = v___y_1017_;
v___y_1131_ = v___y_1018_;
v___y_1132_ = v___y_1019_;
goto v___jp_1128_;
}
v___jp_1021_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; size_t v_sz_1035_; size_t v___x_1036_; lean_object* v___x_8181__overap_1037_; lean_object* v___x_1038_; 
v___x_1030_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1);
v___x_1031_ = lean_mk_array(v___y_1025_, v___x_1030_);
v___x_1032_ = lean_array_get_size(v___y_1023_);
v___x_1033_ = l_Array_toSubarray___redArg(v___y_1023_, v___y_1022_, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1031_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v_sz_1035_ = lean_array_size(v_positions_999_);
v___x_1036_ = ((size_t)0ULL);
lean_inc_ref(v___x_1000_);
v___x_8181__overap_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1000_, v_positions_999_, v___f_1001_, v_sz_1035_, v___x_1036_, v___x_1034_);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
v___x_1038_ = lean_apply_5(v___x_8181__overap_1037_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, lean_box(0));
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v_fst_1040_; size_t v_sz_1041_; lean_object* v___x_8184__overap_1042_; lean_object* v___x_1043_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref(v___x_1038_);
v_fst_1040_ = lean_ctor_get(v_a_1039_, 0);
lean_inc(v_fst_1040_);
lean_dec(v_a_1039_);
v_sz_1041_ = lean_array_size(v_fst_1040_);
lean_inc_ref(v___x_1000_);
v___x_8184__overap_1042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1000_, v___f_1002_, v_sz_1041_, v___x_1036_, v_fst_1040_);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
v___x_1043_ = lean_apply_5(v___x_8184__overap_1042_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, lean_box(0));
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; uint8_t v___x_1045_; lean_object* v___x_8188__overap_1046_; lean_object* v___x_1047_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = 0;
v___x_8188__overap_1046_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1003_, v___x_1000_, v_a_1044_, v___y_1024_, v___x_1045_);
v___x_1047_ = lean_apply_5(v___x_8188__overap_1046_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, lean_box(0));
return v___x_1047_;
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v___x_1000_);
v_a_1048_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1043_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1043_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v___x_1000_);
v_a_1056_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1038_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1038_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
v___jp_1064_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = l_Subarray_copy___redArg(v___y_1069_);
v___x_1073_ = l_Lean_mkAppN(v_f_1014_, v___x_1072_);
lean_dec_ref(v___x_1072_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1068_);
lean_inc_ref(v___x_1073_);
v___x_1074_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1004_, v___x_1073_, v___y_1068_, v___y_1070_, v___y_1067_, v___y_1066_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_8209__overap_1076_; lean_object* v___x_1077_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1074_);
lean_inc(v___x_1007_);
lean_inc(v___x_1006_);
lean_inc_ref(v___x_1005_);
lean_inc_ref(v___x_1000_);
v___x_8209__overap_1076_ = l_Lean_isTracingEnabledFor___redArg(v___x_1000_, v___x_1005_, v___x_1006_, v___x_1007_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1068_);
v___x_1077_ = lean_apply_5(v___x_8209__overap_1076_, v___y_1068_, v___y_1070_, v___y_1067_, v___y_1066_, lean_box(0));
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v_lower_1079_; lean_object* v_upper_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1111_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref(v___x_1077_);
v_lower_1079_ = lean_ctor_get(v___y_1071_, 0);
v_upper_1080_ = lean_ctor_get(v___y_1071_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___y_1071_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1082_ = v___y_1071_;
v_isShared_1083_ = v_isSharedCheck_1111_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_upper_1080_);
lean_inc(v_lower_1079_);
lean_dec(v___y_1071_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1111_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1084_ = l_Array_toSubarray___redArg(v_args_1015_, v_lower_1079_, v_upper_1080_);
lean_inc(v___f_1011_);
lean_inc(v___x_1010_);
lean_inc(v___x_1007_);
lean_inc_ref(v___x_1005_);
lean_inc(v_a_1075_);
lean_inc_ref(v_positions_999_);
lean_inc_ref(v___x_1000_);
v___f_1085_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed), 18, 12);
lean_closure_set(v___f_1085_, 0, v___x_1000_);
lean_closure_set(v___f_1085_, 1, v___x_1008_);
lean_closure_set(v___f_1085_, 2, v_positions_999_);
lean_closure_set(v___f_1085_, 3, v_a_1075_);
lean_closure_set(v___f_1085_, 4, v___x_1005_);
lean_closure_set(v___f_1085_, 5, v___x_1006_);
lean_closure_set(v___f_1085_, 6, v___x_1007_);
lean_closure_set(v___f_1085_, 7, v___x_1073_);
lean_closure_set(v___f_1085_, 8, v___x_1084_);
lean_closure_set(v___f_1085_, 9, v_k_1009_);
lean_closure_set(v___f_1085_, 10, v___x_1010_);
lean_closure_set(v___f_1085_, 11, v___f_1011_);
v___x_1086_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_999_);
v___x_1087_ = lean_unbox(v_a_1078_);
lean_dec(v_a_1078_);
if (v___x_1087_ == 0)
{
lean_del_object(v___x_1082_);
lean_dec(v___f_1011_);
lean_dec(v___x_1010_);
lean_dec(v___x_1007_);
lean_dec_ref(v___x_1005_);
v___y_1022_ = v___y_1065_;
v___y_1023_ = v_a_1075_;
v___y_1024_ = v___f_1085_;
v___y_1025_ = v___x_1086_;
v___y_1026_ = v___y_1068_;
v___y_1027_ = v___y_1070_;
v___y_1028_ = v___y_1067_;
v___y_1029_ = v___y_1066_;
goto v___jp_1021_;
}
else
{
lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v_toMonadRef_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___f_1088_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_1089_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1090_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1088_, v___x_1010_, v___x_1089_);
v___x_1091_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1088_, v___f_1011_, v___x_1090_);
v_toMonadRef_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_toMonadRef_1092_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1094_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3);
lean_inc(v___x_1086_);
v___x_1095_ = l_Nat_reprFast(v___x_1086_);
v___x_1096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
v___x_1097_ = l_Lean_MessageData_ofFormat(v___x_1096_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 7);
lean_ctor_set(v___x_1082_, 1, v___x_1097_);
lean_ctor_set(v___x_1082_, 0, v___x_1094_);
v___x_1099_ = v___x_1082_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_8227__overap_1100_; lean_object* v___x_1101_; 
lean_inc_ref(v___x_1000_);
v___x_8227__overap_1100_ = l_Lean_addTrace___redArg(v___x_1000_, v___x_1005_, v_toMonadRef_1092_, v___x_1093_, v___x_1007_, v___x_1099_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1068_);
v___x_1101_ = lean_apply_5(v___x_8227__overap_1100_, v___y_1068_, v___y_1070_, v___y_1067_, v___y_1066_, lean_box(0));
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_dec_ref(v___x_1101_);
v___y_1022_ = v___y_1065_;
v___y_1023_ = v_a_1075_;
v___y_1024_ = v___f_1085_;
v___y_1025_ = v___x_1086_;
v___y_1026_ = v___y_1068_;
v___y_1027_ = v___y_1070_;
v___y_1028_ = v___y_1067_;
v___y_1029_ = v___y_1066_;
goto v___jp_1021_;
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v___x_1086_);
lean_dec_ref(v___f_1085_);
lean_dec(v_a_1075_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v___x_1000_);
lean_dec_ref(v_positions_999_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v_a_1075_);
lean_dec_ref(v___x_1073_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v_args_1015_);
lean_dec(v___f_1011_);
lean_dec(v___x_1010_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v___x_1008_);
lean_dec(v___x_1007_);
lean_dec(v___x_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v___x_1000_);
lean_dec_ref(v_positions_999_);
v_a_1112_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1077_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1077_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___x_1073_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v_args_1015_);
lean_dec(v___f_1011_);
lean_dec(v___x_1010_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v___x_1008_);
lean_dec(v___x_1007_);
lean_dec(v___x_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v___x_1000_);
lean_dec_ref(v_positions_999_);
v_a_1120_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1074_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1074_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
v___jp_1128_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1012_);
lean_inc_ref(v_args_1015_);
v___x_1134_ = l_Array_toSubarray___redArg(v_args_1015_, v___x_1133_, v_numIndParams_1012_);
v___x_1135_ = lean_nat_add(v_numIndParams_1012_, v_numTypeFormers_1004_);
lean_dec(v_numIndParams_1012_);
v___x_1136_ = lean_array_get_size(v_args_1015_);
v___x_1137_ = lean_nat_dec_le(v___x_1135_, v___x_1133_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1135_);
lean_ctor_set(v___x_1138_, 1, v___x_1136_);
v___y_1065_ = v___x_1133_;
v___y_1066_ = v___y_1132_;
v___y_1067_ = v___y_1131_;
v___y_1068_ = v___y_1129_;
v___y_1069_ = v___x_1134_;
v___y_1070_ = v___y_1130_;
v___y_1071_ = v___x_1138_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1139_; 
lean_dec(v___x_1135_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1133_);
lean_ctor_set(v___x_1139_, 1, v___x_1136_);
v___y_1065_ = v___x_1133_;
v___y_1066_ = v___y_1132_;
v___y_1067_ = v___y_1131_;
v___y_1068_ = v___y_1129_;
v___y_1069_ = v___x_1134_;
v___y_1070_ = v___y_1130_;
v___y_1071_ = v___x_1139_;
goto v___jp_1064_;
}
}
v___jp_1140_:
{
lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v___x_1145_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_positions_1188_ = _args[0];
lean_object* v___x_1189_ = _args[1];
lean_object* v___f_1190_ = _args[2];
lean_object* v___f_1191_ = _args[3];
lean_object* v___x_1192_ = _args[4];
lean_object* v_numTypeFormers_1193_ = _args[5];
lean_object* v___x_1194_ = _args[6];
lean_object* v___x_1195_ = _args[7];
lean_object* v___x_1196_ = _args[8];
lean_object* v___x_1197_ = _args[9];
lean_object* v_k_1198_ = _args[10];
lean_object* v___x_1199_ = _args[11];
lean_object* v___f_1200_ = _args[12];
lean_object* v_numIndParams_1201_ = _args[13];
lean_object* v_a_1202_ = _args[14];
lean_object* v_f_1203_ = _args[15];
lean_object* v_args_1204_ = _args[16];
lean_object* v___y_1205_ = _args[17];
lean_object* v___y_1206_ = _args[18];
lean_object* v___y_1207_ = _args[19];
lean_object* v___y_1208_ = _args[20];
lean_object* v___y_1209_ = _args[21];
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v_positions_1188_, v___x_1189_, v___f_1190_, v___f_1191_, v___x_1192_, v_numTypeFormers_1193_, v___x_1194_, v___x_1195_, v___x_1196_, v___x_1197_, v_k_1198_, v___x_1199_, v___f_1200_, v_numIndParams_1201_, v_a_1202_, v_f_1203_, v_args_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v_res_1210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1213_ = l_ReaderT_instMonad___redArg(v___x_1212_);
return v___x_1213_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1221_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1222_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1225_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1224_, v___x_1223_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___f_1234_; lean_object* v___x_1235_; 
v___x_1232_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___f_1234_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_1235_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1234_, v___x_1233_, v___x_1232_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; 
v___x_1236_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14);
v___f_1237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1238_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_1239_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1238_, v___f_1237_, v___x_1236_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1243_, lean_object* v_numIndParams_1244_, lean_object* v_positions_1245_, lean_object* v_k_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v_toApplicative_1253_; lean_object* v_toFunctor_1254_; lean_object* v_toSeq_1255_; lean_object* v_toSeqLeft_1256_; lean_object* v_toSeqRight_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1435_; 
v___x_1252_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc_ref(v_toApplicative_1253_);
v_toFunctor_1254_ = lean_ctor_get(v_toApplicative_1253_, 0);
v_toSeq_1255_ = lean_ctor_get(v_toApplicative_1253_, 2);
v_toSeqLeft_1256_ = lean_ctor_get(v_toApplicative_1253_, 3);
v_toSeqRight_1257_ = lean_ctor_get(v_toApplicative_1253_, 4);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_toApplicative_1253_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_toApplicative_1253_, 1);
lean_dec(v_unused_1436_);
v___x_1259_ = v_toApplicative_1253_;
v_isShared_1260_ = v_isSharedCheck_1435_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_toSeqRight_1257_);
lean_inc(v_toSeqLeft_1256_);
lean_inc(v_toSeq_1255_);
lean_inc(v_toFunctor_1254_);
lean_dec(v_toApplicative_1253_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1435_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___x_1270_; 
v___f_1261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref(v_toFunctor_1254_);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toFunctor_1254_);
v___f_1264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1264_, 0, v_toFunctor_1254_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___f_1263_);
lean_ctor_set(v___x_1265_, 1, v___f_1264_);
v___f_1266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1266_, 0, v_toSeqRight_1257_);
v___f_1267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1267_, 0, v_toSeqLeft_1256_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toSeq_1255_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 4, v___f_1266_);
lean_ctor_set(v___x_1259_, 3, v___f_1267_);
lean_ctor_set(v___x_1259_, 2, v___f_1268_);
lean_ctor_set(v___x_1259_, 1, v___f_1261_);
lean_ctor_set(v___x_1259_, 0, v___x_1265_);
v___x_1270_ = v___x_1259_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___f_1261_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v___f_1268_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v___f_1267_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v___f_1266_);
v___x_1270_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_toApplicative_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1432_; 
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___f_1262_);
v___x_1272_ = l_ReaderT_instMonad___redArg(v___x_1271_);
v_toApplicative_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v___x_1272_, 1);
lean_dec(v_unused_1433_);
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1432_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_toApplicative_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1432_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_toFunctor_1277_; lean_object* v_toSeq_1278_; lean_object* v_toSeqLeft_1279_; lean_object* v_toSeqRight_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1430_; 
v_toFunctor_1277_ = lean_ctor_get(v_toApplicative_1273_, 0);
v_toSeq_1278_ = lean_ctor_get(v_toApplicative_1273_, 2);
v_toSeqLeft_1279_ = lean_ctor_get(v_toApplicative_1273_, 3);
v_toSeqRight_1280_ = lean_ctor_get(v_toApplicative_1273_, 4);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_toApplicative_1273_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v_toApplicative_1273_, 1);
lean_dec(v_unused_1431_);
v___x_1282_ = v_toApplicative_1273_;
v_isShared_1283_ = v_isSharedCheck_1430_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_toSeqRight_1280_);
lean_inc(v_toSeqLeft_1279_);
lean_inc(v_toSeq_1278_);
lean_inc(v_toFunctor_1277_);
lean_dec(v_toApplicative_1273_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1430_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___f_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___f_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___x_1293_; 
v___f_1284_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1285_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1277_);
v___f_1286_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1286_, 0, v_toFunctor_1277_);
v___f_1287_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1287_, 0, v_toFunctor_1277_);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___f_1286_);
lean_ctor_set(v___x_1288_, 1, v___f_1287_);
v___f_1289_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1289_, 0, v_toSeqRight_1280_);
v___f_1290_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1290_, 0, v_toSeqLeft_1279_);
v___f_1291_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1291_, 0, v_toSeq_1278_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 4, v___f_1289_);
lean_ctor_set(v___x_1282_, 3, v___f_1290_);
lean_ctor_set(v___x_1282_, 2, v___f_1291_);
lean_ctor_set(v___x_1282_, 1, v___f_1284_);
lean_ctor_set(v___x_1282_, 0, v___x_1288_);
v___x_1293_ = v___x_1282_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___f_1284_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v___f_1291_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v___f_1290_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v___f_1289_);
v___x_1293_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___f_1285_);
lean_ctor_set(v___x_1275_, 0, v___x_1293_);
v___x_1295_ = v___x_1275_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___f_1285_);
v___x_1295_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_toApplicative_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1426_; 
v___f_1296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1297_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1298_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1299_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1252_, 1);
lean_dec(v_unused_1427_);
v___x_1301_ = v___x_1252_;
v_isShared_1302_ = v_isSharedCheck_1426_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_toApplicative_1299_);
lean_dec(v___x_1252_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1426_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v_toFunctor_1303_; lean_object* v_toSeq_1304_; lean_object* v_toSeqLeft_1305_; lean_object* v_toSeqRight_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1424_; 
v_toFunctor_1303_ = lean_ctor_get(v_toApplicative_1299_, 0);
v_toSeq_1304_ = lean_ctor_get(v_toApplicative_1299_, 2);
v_toSeqLeft_1305_ = lean_ctor_get(v_toApplicative_1299_, 3);
v_toSeqRight_1306_ = lean_ctor_get(v_toApplicative_1299_, 4);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_toApplicative_1299_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v_toApplicative_1299_, 1);
lean_dec(v_unused_1425_);
v___x_1308_ = v_toApplicative_1299_;
v_isShared_1309_ = v_isSharedCheck_1424_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_toSeqRight_1306_);
lean_inc(v_toSeqLeft_1305_);
lean_inc(v_toSeq_1304_);
lean_inc(v_toFunctor_1303_);
lean_dec(v_toApplicative_1299_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1424_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___f_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___f_1313_; lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v___x_1317_; 
lean_inc_ref(v_toFunctor_1303_);
v___f_1310_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1310_, 0, v_toFunctor_1303_);
v___f_1311_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1311_, 0, v_toFunctor_1303_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___f_1310_);
lean_ctor_set(v___x_1312_, 1, v___f_1311_);
v___f_1313_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1313_, 0, v_toSeqRight_1306_);
v___f_1314_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1314_, 0, v_toSeqLeft_1305_);
v___f_1315_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1315_, 0, v_toSeq_1304_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 4, v___f_1313_);
lean_ctor_set(v___x_1308_, 3, v___f_1314_);
lean_ctor_set(v___x_1308_, 2, v___f_1315_);
lean_ctor_set(v___x_1308_, 1, v___f_1261_);
lean_ctor_set(v___x_1308_, 0, v___x_1312_);
v___x_1317_ = v___x_1308_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___f_1261_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v___f_1315_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v___f_1314_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v___f_1313_);
v___x_1317_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1319_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v___f_1262_);
lean_ctor_set(v___x_1301_, 0, v___x_1317_);
v___x_1319_ = v___x_1301_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___f_1262_);
v___x_1319_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = l_ReaderT_instMonad___redArg(v___x_1319_);
v___x_1321_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1321_, 0, lean_box(0));
lean_closure_set(v___x_1321_, 1, lean_box(0));
lean_closure_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = l_instMonadControlTOfPure___redArg(v___x_1321_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc_ref(v_below_1243_);
v___x_1323_ = lean_infer_type(v_below_1243_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_7223__overap_1327_; lean_object* v___x_1328_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12));
v___x_1326_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
lean_inc_ref(v___x_1295_);
v___x_7223__overap_1327_ = l_Lean_isTracingEnabledFor___redArg(v___x_1295_, v___x_1298_, v___x_1325_, v___x_1326_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
v___x_1328_ = lean_apply_5(v___x_7223__overap_1327_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, lean_box(0));
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___x_1332_; lean_object* v_numTypeFormers_1333_; lean_object* v___f_1334_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; uint8_t v___x_1389_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1328_);
v___f_1330_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13));
lean_inc_ref(v___x_1295_);
v___f_1331_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_1331_, 0, v___x_1295_);
v___x_1332_ = l_Lean_instInhabitedExpr;
v_numTypeFormers_1333_ = lean_array_get_size(v_positions_1245_);
lean_inc(v_a_1324_);
lean_inc_ref(v___x_1295_);
v___f_1334_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 22, 15);
lean_closure_set(v___f_1334_, 0, v_positions_1245_);
lean_closure_set(v___f_1334_, 1, v___x_1295_);
lean_closure_set(v___f_1334_, 2, v___f_1331_);
lean_closure_set(v___f_1334_, 3, v___f_1330_);
lean_closure_set(v___f_1334_, 4, v___x_1322_);
lean_closure_set(v___f_1334_, 5, v_numTypeFormers_1333_);
lean_closure_set(v___f_1334_, 6, v___x_1298_);
lean_closure_set(v___f_1334_, 7, v___x_1325_);
lean_closure_set(v___f_1334_, 8, v___x_1326_);
lean_closure_set(v___f_1334_, 9, v___x_1332_);
lean_closure_set(v___f_1334_, 10, v_k_1246_);
lean_closure_set(v___f_1334_, 11, v___x_1297_);
lean_closure_set(v___f_1334_, 12, v___f_1296_);
lean_closure_set(v___f_1334_, 13, v_numIndParams_1244_);
lean_closure_set(v___f_1334_, 14, v_a_1324_);
v___x_1389_ = lean_unbox(v_a_1329_);
lean_dec(v_a_1329_);
if (v___x_1389_ == 0)
{
v___y_1348_ = v_a_1247_;
v___y_1349_ = v_a_1248_;
v___y_1350_ = v_a_1249_;
v___y_1351_ = v_a_1250_;
goto v___jp_1347_;
}
else
{
lean_object* v___x_1390_; lean_object* v_toMonadRef_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_7878__overap_1396_; lean_object* v___x_1397_; 
v___x_1390_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15);
v_toMonadRef_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc_ref(v_toMonadRef_1391_);
v___x_1392_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1393_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17);
lean_inc(v_a_1324_);
v___x_1394_ = l_Lean_MessageData_ofExpr(v_a_1324_);
v___x_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
lean_inc_ref(v___x_1295_);
v___x_7878__overap_1396_ = l_Lean_addTrace___redArg(v___x_1295_, v___x_1298_, v_toMonadRef_1391_, v___x_1392_, v___x_1326_, v___x_1395_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
v___x_1397_ = lean_apply_5(v___x_7878__overap_1396_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, lean_box(0));
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_dec_ref(v___x_1397_);
v___y_1348_ = v_a_1247_;
v___y_1349_ = v_a_1248_;
v___y_1350_ = v_a_1249_;
v___y_1351_ = v_a_1250_;
goto v___jp_1347_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v___f_1334_);
lean_dec(v_a_1324_);
lean_dec_ref(v___x_1295_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec_ref(v_below_1243_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
v___jp_1335_:
{
lean_object* v_dummy_1340_; lean_object* v_nargs_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_7597__overap_1345_; lean_object* v___x_1346_; 
v_dummy_1340_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
v_nargs_1341_ = l_Lean_Expr_getAppNumArgs(v_a_1324_);
lean_inc(v_nargs_1341_);
v___x_1342_ = lean_mk_array(v_nargs_1341_, v_dummy_1340_);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_nat_sub(v_nargs_1341_, v___x_1343_);
lean_dec(v_nargs_1341_);
v___x_7597__overap_1345_ = l_Lean_Expr_withAppAux___redArg(v___f_1334_, v_a_1324_, v___x_1342_, v___x_1344_);
v___x_1346_ = lean_apply_5(v___x_7597__overap_1345_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1346_;
}
v___jp_1347_:
{
lean_object* v___x_1352_; 
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1352_ = l_Lean_Meta_isTypeCorrect(v_below_1243_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; uint8_t v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = lean_unbox(v_a_1353_);
lean_dec(v_a_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_7819__overap_1355_; lean_object* v___x_1356_; 
lean_inc_ref(v___x_1295_);
v___x_7819__overap_1355_ = l_Lean_isTracingEnabledFor___redArg(v___x_1295_, v___x_1298_, v___x_1325_, v___x_1326_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1356_ = lean_apply_5(v___x_7819__overap_1355_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, lean_box(0));
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; uint8_t v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = lean_unbox(v_a_1357_);
lean_dec(v_a_1357_);
if (v___x_1358_ == 0)
{
lean_dec_ref(v___x_1295_);
v___y_1336_ = v___y_1348_;
v___y_1337_ = v___y_1349_;
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1351_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1359_; lean_object* v_toMonadRef_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_7856__overap_1363_; lean_object* v___x_1364_; 
v___x_1359_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15);
v_toMonadRef_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc_ref(v_toMonadRef_1360_);
v___x_1361_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1362_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3);
v___x_7856__overap_1363_ = l_Lean_addTrace___redArg(v___x_1295_, v___x_1298_, v_toMonadRef_1360_, v___x_1361_, v___x_1326_, v___x_1362_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1364_ = lean_apply_5(v___x_7856__overap_1363_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, lean_box(0));
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_dec_ref(v___x_1364_);
v___y_1336_ = v___y_1348_;
v___y_1337_ = v___y_1349_;
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1351_;
goto v___jp_1335_;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v___f_1334_);
lean_dec(v_a_1324_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v___f_1334_);
lean_dec(v_a_1324_);
lean_dec_ref(v___x_1295_);
v_a_1373_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1356_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1356_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
else
{
lean_dec_ref(v___x_1295_);
v___y_1336_ = v___y_1348_;
v___y_1337_ = v___y_1349_;
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1351_;
goto v___jp_1335_;
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v___f_1334_);
lean_dec(v_a_1324_);
lean_dec_ref(v___x_1295_);
v_a_1381_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1352_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1352_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_a_1324_);
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1295_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec_ref(v_k_1246_);
lean_dec_ref(v_positions_1245_);
lean_dec(v_numIndParams_1244_);
lean_dec_ref(v_below_1243_);
v_a_1406_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1328_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1328_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1295_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec_ref(v_k_1246_);
lean_dec_ref(v_positions_1245_);
lean_dec(v_numIndParams_1244_);
lean_dec_ref(v_below_1243_);
v_a_1414_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1323_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1323_);
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
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1437_, lean_object* v_numIndParams_1438_, lean_object* v_positions_1439_, lean_object* v_k_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1437_, v_numIndParams_1438_, v_positions_1439_, v_k_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1447_, lean_object* v_inst_1448_, lean_object* v_below_1449_, lean_object* v_numIndParams_1450_, lean_object* v_positions_1451_, lean_object* v_k_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1449_, v_numIndParams_1450_, v_positions_1451_, v_k_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1459_, lean_object* v_inst_1460_, lean_object* v_below_1461_, lean_object* v_numIndParams_1462_, lean_object* v_positions_1463_, lean_object* v_k_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1459_, v_inst_1460_, v_below_1461_, v_numIndParams_1462_, v_positions_1463_, v_k_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_inst_1460_);
return v_res_1470_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(32u);
v___x_1472_ = lean_mk_empty_array_with_capacity(v___x_1471_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1474_ = ((size_t)5ULL);
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_unsigned_to_nat(32u);
v___x_1477_ = lean_mk_empty_array_with_capacity(v___x_1476_);
v___x_1478_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1479_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1477_);
lean_ctor_set(v___x_1479_, 2, v___x_1475_);
lean_ctor_set(v___x_1479_, 3, v___x_1475_);
lean_ctor_set_usize(v___x_1479_, 4, v___x_1474_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; lean_object* v_traceState_1483_; lean_object* v_traces_1484_; lean_object* v___x_1485_; lean_object* v_traceState_1486_; lean_object* v_env_1487_; lean_object* v_nextMacroScope_1488_; lean_object* v_ngen_1489_; lean_object* v_auxDeclNGen_1490_; lean_object* v_cache_1491_; lean_object* v_messages_1492_; lean_object* v_infoState_1493_; lean_object* v_snapshotTasks_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1513_; 
v___x_1482_ = lean_st_ref_get(v___y_1480_);
v_traceState_1483_ = lean_ctor_get(v___x_1482_, 4);
lean_inc_ref(v_traceState_1483_);
lean_dec(v___x_1482_);
v_traces_1484_ = lean_ctor_get(v_traceState_1483_, 0);
lean_inc_ref(v_traces_1484_);
lean_dec_ref(v_traceState_1483_);
v___x_1485_ = lean_st_ref_take(v___y_1480_);
v_traceState_1486_ = lean_ctor_get(v___x_1485_, 4);
v_env_1487_ = lean_ctor_get(v___x_1485_, 0);
v_nextMacroScope_1488_ = lean_ctor_get(v___x_1485_, 1);
v_ngen_1489_ = lean_ctor_get(v___x_1485_, 2);
v_auxDeclNGen_1490_ = lean_ctor_get(v___x_1485_, 3);
v_cache_1491_ = lean_ctor_get(v___x_1485_, 5);
v_messages_1492_ = lean_ctor_get(v___x_1485_, 6);
v_infoState_1493_ = lean_ctor_get(v___x_1485_, 7);
v_snapshotTasks_1494_ = lean_ctor_get(v___x_1485_, 8);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1496_ = v___x_1485_;
v_isShared_1497_ = v_isSharedCheck_1513_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snapshotTasks_1494_);
lean_inc(v_infoState_1493_);
lean_inc(v_messages_1492_);
lean_inc(v_cache_1491_);
lean_inc(v_traceState_1486_);
lean_inc(v_auxDeclNGen_1490_);
lean_inc(v_ngen_1489_);
lean_inc(v_nextMacroScope_1488_);
lean_inc(v_env_1487_);
lean_dec(v___x_1485_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1513_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
uint64_t v_tid_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1511_; 
v_tid_1498_ = lean_ctor_get_uint64(v_traceState_1486_, sizeof(void*)*1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_traceState_1486_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v_traceState_1486_, 0);
lean_dec(v_unused_1512_);
v___x_1500_ = v_traceState_1486_;
v_isShared_1501_ = v_isSharedCheck_1511_;
goto v_resetjp_1499_;
}
else
{
lean_dec(v_traceState_1486_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1511_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1502_);
v___x_1504_ = v___x_1500_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1502_);
lean_ctor_set_uint64(v_reuseFailAlloc_1510_, sizeof(void*)*1, v_tid_1498_);
v___x_1504_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 4, v___x_1504_);
v___x_1506_ = v___x_1496_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_env_1487_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_nextMacroScope_1488_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_ngen_1489_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_auxDeclNGen_1490_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1509_, 5, v_cache_1491_);
lean_ctor_set(v_reuseFailAlloc_1509_, 6, v_messages_1492_);
lean_ctor_set(v_reuseFailAlloc_1509_, 7, v_infoState_1493_);
lean_ctor_set(v_reuseFailAlloc_1509_, 8, v_snapshotTasks_1494_);
v___x_1506_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_st_ref_set(v___y_1480_, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_traces_1484_);
return v___x_1508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1514_);
lean_dec(v___y_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1529_, lean_object* v_opt_1530_){
_start:
{
lean_object* v_name_1531_; lean_object* v_defValue_1532_; lean_object* v_map_1533_; lean_object* v___x_1534_; 
v_name_1531_ = lean_ctor_get(v_opt_1530_, 0);
v_defValue_1532_ = lean_ctor_get(v_opt_1530_, 1);
v_map_1533_ = lean_ctor_get(v_opts_1529_, 0);
v___x_1534_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1533_, v_name_1531_);
if (lean_obj_tag(v___x_1534_) == 0)
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_unbox(v_defValue_1532_);
return v___x_1535_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_val_1536_);
lean_dec_ref(v___x_1534_);
if (lean_obj_tag(v_val_1536_) == 1)
{
uint8_t v_v_1537_; 
v_v_1537_ = lean_ctor_get_uint8(v_val_1536_, 0);
lean_dec_ref(v_val_1536_);
return v_v_1537_;
}
else
{
uint8_t v___x_1538_; 
lean_dec(v_val_1536_);
v___x_1538_ = lean_unbox(v_defValue_1532_);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1539_, lean_object* v_opt_1540_){
_start:
{
uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_res_1541_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1539_, v_opt_1540_);
lean_dec_ref(v_opt_1540_);
lean_dec_ref(v_opts_1539_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1543_, lean_object* v_fnIndex_1544_, lean_object* v_recArg_1545_, lean_object* v_below_1546_, lean_object* v_Cs_1547_, lean_object* v_belowDict_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_array_get_borrowed(v___x_1543_, v_Cs_1547_, v_fnIndex_1544_);
lean_inc(v___x_1554_);
v___x_1555_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1554_, v_belowDict_1548_, v_recArg_1545_, v_below_1546_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1556_, lean_object* v_fnIndex_1557_, lean_object* v_recArg_1558_, lean_object* v_below_1559_, lean_object* v_Cs_1560_, lean_object* v_belowDict_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1556_, v_fnIndex_1557_, v_recArg_1558_, v_below_1559_, v_Cs_1560_, v_belowDict_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec_ref(v_Cs_1560_);
lean_dec(v_fnIndex_1557_);
return v_res_1567_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1574_, lean_object* v_recArg_1575_, lean_object* v_x_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_infer_type(v_below_1574_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1597_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1597_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1597_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1587_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1588_ = l_Lean_MessageData_ofExpr(v_recArg_1575_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_MessageData_ofExpr(v_a_1583_);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1593_);
v___x_1595_ = v___x_1585_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec_ref(v_recArg_1575_);
v_a_1598_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1582_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1582_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1606_, lean_object* v_recArg_1607_, lean_object* v_x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1606_, v_recArg_1607_, v_x_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec_ref(v_x_1608_);
return v_res_1614_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_e_1615_){
_start:
{
if (lean_obj_tag(v_e_1615_) == 0)
{
uint8_t v___x_1616_; 
v___x_1616_ = 2;
return v___x_1616_;
}
else
{
uint8_t v___x_1617_; 
v___x_1617_ = 0;
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_e_1618_){
_start:
{
uint8_t v_res_1619_; lean_object* v_r_1620_; 
v_res_1619_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_e_1618_);
lean_dec_ref(v_e_1618_);
v_r_1620_ = lean_box(v_res_1619_);
return v_r_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1621_, lean_object* v_opt_1622_){
_start:
{
lean_object* v_name_1623_; lean_object* v_defValue_1624_; lean_object* v_map_1625_; lean_object* v___x_1626_; 
v_name_1623_ = lean_ctor_get(v_opt_1622_, 0);
v_defValue_1624_ = lean_ctor_get(v_opt_1622_, 1);
v_map_1625_ = lean_ctor_get(v_opts_1621_, 0);
v___x_1626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1625_, v_name_1623_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_inc(v_defValue_1624_);
return v_defValue_1624_;
}
else
{
lean_object* v_val_1627_; 
v_val_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_val_1627_);
lean_dec_ref(v___x_1626_);
if (lean_obj_tag(v_val_1627_) == 3)
{
lean_object* v_v_1628_; 
v_v_1628_ = lean_ctor_get(v_val_1627_, 0);
lean_inc(v_v_1628_);
lean_dec_ref(v_val_1627_);
return v_v_1628_;
}
else
{
lean_dec(v_val_1627_);
lean_inc(v_defValue_1624_);
return v_defValue_1624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1629_, lean_object* v_opt_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1629_, v_opt_1630_);
lean_dec_ref(v_opt_1630_);
lean_dec_ref(v_opts_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_a_1634_ = lean_ctor_get(v_x_1632_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_x_1632_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v_x_1632_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v_x_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 1);
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v_x_1632_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_x_1632_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v_x_1632_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v_x_1632_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 0);
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg___boxed(lean_object* v_x_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_x_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(size_t v_sz_1653_, size_t v_i_1654_, lean_object* v_bs_1655_){
_start:
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_usize_dec_lt(v_i_1654_, v_sz_1653_);
if (v___x_1656_ == 0)
{
return v_bs_1655_;
}
else
{
lean_object* v_v_1657_; lean_object* v_msg_1658_; lean_object* v___x_1659_; lean_object* v_bs_x27_1660_; size_t v___x_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v_v_1657_ = lean_array_uget_borrowed(v_bs_1655_, v_i_1654_);
v_msg_1658_ = lean_ctor_get(v_v_1657_, 1);
lean_inc_ref(v_msg_1658_);
v___x_1659_ = lean_unsigned_to_nat(0u);
v_bs_x27_1660_ = lean_array_uset(v_bs_1655_, v_i_1654_, v___x_1659_);
v___x_1661_ = ((size_t)1ULL);
v___x_1662_ = lean_usize_add(v_i_1654_, v___x_1661_);
v___x_1663_ = lean_array_uset(v_bs_x27_1660_, v_i_1654_, v_msg_1658_);
v_i_1654_ = v___x_1662_;
v_bs_1655_ = v___x_1663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_1665_, lean_object* v_i_1666_, lean_object* v_bs_1667_){
_start:
{
size_t v_sz_boxed_1668_; size_t v_i_boxed_1669_; lean_object* v_res_1670_; 
v_sz_boxed_1668_ = lean_unbox_usize(v_sz_1665_);
lean_dec(v_sz_1665_);
v_i_boxed_1669_ = lean_unbox_usize(v_i_1666_);
lean_dec(v_i_1666_);
v_res_1670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(v_sz_boxed_1668_, v_i_boxed_1669_, v_bs_1667_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_oldTraces_1671_, lean_object* v_data_1672_, lean_object* v_ref_1673_, lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_fileName_1680_; lean_object* v_fileMap_1681_; lean_object* v_options_1682_; lean_object* v_currRecDepth_1683_; lean_object* v_maxRecDepth_1684_; lean_object* v_ref_1685_; lean_object* v_currNamespace_1686_; lean_object* v_openDecls_1687_; lean_object* v_initHeartbeats_1688_; lean_object* v_maxHeartbeats_1689_; lean_object* v_quotContext_1690_; lean_object* v_currMacroScope_1691_; uint8_t v_diag_1692_; lean_object* v_cancelTk_x3f_1693_; uint8_t v_suppressElabErrors_1694_; lean_object* v_inheritedTraceOptions_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1750_; 
v_fileName_1680_ = lean_ctor_get(v___y_1677_, 0);
v_fileMap_1681_ = lean_ctor_get(v___y_1677_, 1);
v_options_1682_ = lean_ctor_get(v___y_1677_, 2);
v_currRecDepth_1683_ = lean_ctor_get(v___y_1677_, 3);
v_maxRecDepth_1684_ = lean_ctor_get(v___y_1677_, 4);
v_ref_1685_ = lean_ctor_get(v___y_1677_, 5);
v_currNamespace_1686_ = lean_ctor_get(v___y_1677_, 6);
v_openDecls_1687_ = lean_ctor_get(v___y_1677_, 7);
v_initHeartbeats_1688_ = lean_ctor_get(v___y_1677_, 8);
v_maxHeartbeats_1689_ = lean_ctor_get(v___y_1677_, 9);
v_quotContext_1690_ = lean_ctor_get(v___y_1677_, 10);
v_currMacroScope_1691_ = lean_ctor_get(v___y_1677_, 11);
v_diag_1692_ = lean_ctor_get_uint8(v___y_1677_, sizeof(void*)*14);
v_cancelTk_x3f_1693_ = lean_ctor_get(v___y_1677_, 12);
v_suppressElabErrors_1694_ = lean_ctor_get_uint8(v___y_1677_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1695_ = lean_ctor_get(v___y_1677_, 13);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___y_1677_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1697_ = v___y_1677_;
v_isShared_1698_ = v_isSharedCheck_1750_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_inheritedTraceOptions_1695_);
lean_inc(v_cancelTk_x3f_1693_);
lean_inc(v_currMacroScope_1691_);
lean_inc(v_quotContext_1690_);
lean_inc(v_maxHeartbeats_1689_);
lean_inc(v_initHeartbeats_1688_);
lean_inc(v_openDecls_1687_);
lean_inc(v_currNamespace_1686_);
lean_inc(v_ref_1685_);
lean_inc(v_maxRecDepth_1684_);
lean_inc(v_currRecDepth_1683_);
lean_inc(v_options_1682_);
lean_inc(v_fileMap_1681_);
lean_inc(v_fileName_1680_);
lean_dec(v___y_1677_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1750_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v_traceState_1700_; lean_object* v_traces_1701_; lean_object* v_ref_1702_; lean_object* v___x_1704_; 
v___x_1699_ = lean_st_ref_get(v___y_1678_);
v_traceState_1700_ = lean_ctor_get(v___x_1699_, 4);
lean_inc_ref(v_traceState_1700_);
lean_dec(v___x_1699_);
v_traces_1701_ = lean_ctor_get(v_traceState_1700_, 0);
lean_inc_ref(v_traces_1701_);
lean_dec_ref(v_traceState_1700_);
v_ref_1702_ = l_Lean_replaceRef(v_ref_1673_, v_ref_1685_);
lean_dec(v_ref_1685_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 5, v_ref_1702_);
v___x_1704_ = v___x_1697_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_fileName_1680_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_fileMap_1681_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_options_1682_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v_currRecDepth_1683_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_maxRecDepth_1684_);
lean_ctor_set(v_reuseFailAlloc_1749_, 5, v_ref_1702_);
lean_ctor_set(v_reuseFailAlloc_1749_, 6, v_currNamespace_1686_);
lean_ctor_set(v_reuseFailAlloc_1749_, 7, v_openDecls_1687_);
lean_ctor_set(v_reuseFailAlloc_1749_, 8, v_initHeartbeats_1688_);
lean_ctor_set(v_reuseFailAlloc_1749_, 9, v_maxHeartbeats_1689_);
lean_ctor_set(v_reuseFailAlloc_1749_, 10, v_quotContext_1690_);
lean_ctor_set(v_reuseFailAlloc_1749_, 11, v_currMacroScope_1691_);
lean_ctor_set(v_reuseFailAlloc_1749_, 12, v_cancelTk_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1749_, 13, v_inheritedTraceOptions_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1749_, sizeof(void*)*14, v_diag_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1749_, sizeof(void*)*14 + 1, v_suppressElabErrors_1694_);
v___x_1704_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; size_t v_sz_1706_; size_t v___x_1707_; lean_object* v___x_1708_; lean_object* v_msg_1709_; lean_object* v___x_1710_; lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1748_; 
v___x_1705_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1701_);
lean_dec_ref(v_traces_1701_);
v_sz_1706_ = lean_array_size(v___x_1705_);
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(v_sz_1706_, v___x_1707_, v___x_1705_);
v_msg_1709_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1709_, 0, v_data_1672_);
lean_ctor_set(v_msg_1709_, 1, v_msg_1674_);
lean_ctor_set(v_msg_1709_, 2, v___x_1708_);
v___x_1710_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1709_, v___y_1675_, v___y_1676_, v___x_1704_, v___y_1678_);
lean_dec_ref(v___x_1704_);
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1748_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1748_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v_traceState_1716_; lean_object* v_env_1717_; lean_object* v_nextMacroScope_1718_; lean_object* v_ngen_1719_; lean_object* v_auxDeclNGen_1720_; lean_object* v_cache_1721_; lean_object* v_messages_1722_; lean_object* v_infoState_1723_; lean_object* v_snapshotTasks_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1747_; 
v___x_1715_ = lean_st_ref_take(v___y_1678_);
v_traceState_1716_ = lean_ctor_get(v___x_1715_, 4);
v_env_1717_ = lean_ctor_get(v___x_1715_, 0);
v_nextMacroScope_1718_ = lean_ctor_get(v___x_1715_, 1);
v_ngen_1719_ = lean_ctor_get(v___x_1715_, 2);
v_auxDeclNGen_1720_ = lean_ctor_get(v___x_1715_, 3);
v_cache_1721_ = lean_ctor_get(v___x_1715_, 5);
v_messages_1722_ = lean_ctor_get(v___x_1715_, 6);
v_infoState_1723_ = lean_ctor_get(v___x_1715_, 7);
v_snapshotTasks_1724_ = lean_ctor_get(v___x_1715_, 8);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1726_ = v___x_1715_;
v_isShared_1727_ = v_isSharedCheck_1747_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snapshotTasks_1724_);
lean_inc(v_infoState_1723_);
lean_inc(v_messages_1722_);
lean_inc(v_cache_1721_);
lean_inc(v_traceState_1716_);
lean_inc(v_auxDeclNGen_1720_);
lean_inc(v_ngen_1719_);
lean_inc(v_nextMacroScope_1718_);
lean_inc(v_env_1717_);
lean_dec(v___x_1715_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1747_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
uint64_t v_tid_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1745_; 
v_tid_1728_ = lean_ctor_get_uint64(v_traceState_1716_, sizeof(void*)*1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_traceState_1716_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; 
v_unused_1746_ = lean_ctor_get(v_traceState_1716_, 0);
lean_dec(v_unused_1746_);
v___x_1730_ = v_traceState_1716_;
v_isShared_1731_ = v_isSharedCheck_1745_;
goto v_resetjp_1729_;
}
else
{
lean_dec(v_traceState_1716_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1745_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_ref_1673_);
lean_ctor_set(v___x_1732_, 1, v_a_1711_);
v___x_1733_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1671_, v___x_1732_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1733_);
v___x_1735_ = v___x_1730_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1733_);
lean_ctor_set_uint64(v_reuseFailAlloc_1744_, sizeof(void*)*1, v_tid_1728_);
v___x_1735_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 4, v___x_1735_);
v___x_1737_ = v___x_1726_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_env_1717_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_nextMacroScope_1718_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_ngen_1719_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v_auxDeclNGen_1720_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1743_, 5, v_cache_1721_);
lean_ctor_set(v_reuseFailAlloc_1743_, 6, v_messages_1722_);
lean_ctor_set(v_reuseFailAlloc_1743_, 7, v_infoState_1723_);
lean_ctor_set(v_reuseFailAlloc_1743_, 8, v_snapshotTasks_1724_);
v___x_1737_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1738_ = lean_st_ref_set(v___y_1678_, v___x_1737_);
v___x_1739_ = lean_box(0);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1739_);
v___x_1741_ = v___x_1713_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_oldTraces_1751_, lean_object* v_data_1752_, lean_object* v_ref_1753_, lean_object* v_msg_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_oldTraces_1751_, v_data_1752_, v_ref_1753_, v_msg_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1760_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2));
v___x_1766_ = l_Lean_stringToMessageData(v___x_1765_);
return v___x_1766_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1767_; double v___x_1768_; 
v___x_1767_ = lean_unsigned_to_nat(1000u);
v___x_1768_ = lean_float_of_nat(v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1769_, uint8_t v_collapsed_1770_, lean_object* v_tag_1771_, lean_object* v_opts_1772_, uint8_t v_clsEnabled_1773_, lean_object* v_oldTraces_1774_, lean_object* v_msg_1775_, lean_object* v_resStartStop_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_fst_1782_; lean_object* v_snd_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1881_; 
v_fst_1782_ = lean_ctor_get(v_resStartStop_1776_, 0);
v_snd_1783_ = lean_ctor_get(v_resStartStop_1776_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_resStartStop_1776_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1785_ = v_resStartStop_1776_;
v_isShared_1786_ = v_isSharedCheck_1881_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_snd_1783_);
lean_inc(v_fst_1782_);
lean_dec(v_resStartStop_1776_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1881_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v_data_1790_; lean_object* v_fst_1801_; lean_object* v_snd_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1880_; 
v_fst_1801_ = lean_ctor_get(v_snd_1783_, 0);
v_snd_1802_ = lean_ctor_get(v_snd_1783_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_snd_1783_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1804_ = v_snd_1783_;
v_isShared_1805_ = v_isSharedCheck_1880_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_snd_1802_);
lean_inc(v_fst_1801_);
lean_dec(v_snd_1783_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1880_;
goto v_resetjp_1803_;
}
v___jp_1787_:
{
lean_object* v___x_1791_; 
v___x_1791_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_oldTraces_1774_, v_data_1790_, v___y_1789_, v___y_1788_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v___x_1792_; 
lean_dec_ref(v___x_1791_);
v___x_1792_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_fst_1782_);
return v___x_1792_;
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_fst_1782_);
v_a_1793_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1791_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1791_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___y_1809_; lean_object* v_a_1810_; uint8_t v___y_1834_; double v___y_1865_; 
v___x_1806_ = l_Lean_trace_profiler;
v___x_1807_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1772_, v___x_1806_);
if (v___x_1807_ == 0)
{
v___y_1834_ = v___x_1807_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1871_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1772_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; double v___x_1874_; double v___x_1875_; double v___x_1876_; 
v___x_1872_ = l_Lean_trace_profiler_threshold;
v___x_1873_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1772_, v___x_1872_);
v___x_1874_ = lean_float_of_nat(v___x_1873_);
v___x_1875_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4);
v___x_1876_ = lean_float_div(v___x_1874_, v___x_1875_);
v___y_1865_ = v___x_1876_;
goto v___jp_1864_;
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; double v___x_1879_; 
v___x_1877_ = l_Lean_trace_profiler_threshold;
v___x_1878_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1772_, v___x_1877_);
v___x_1879_ = lean_float_of_nat(v___x_1878_);
v___y_1865_ = v___x_1879_;
goto v___jp_1864_;
}
}
v___jp_1808_:
{
uint8_t v_result_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v_result_1811_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_fst_1782_);
v___x_1812_ = l_Lean_TraceResult_toEmoji(v_result_1811_);
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
v___x_1814_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 7);
lean_ctor_set(v___x_1804_, 1, v___x_1814_);
lean_ctor_set(v___x_1804_, 0, v___x_1813_);
v___x_1816_ = v___x_1804_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v_m_1818_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 7);
lean_ctor_set(v___x_1785_, 1, v_a_1810_);
lean_ctor_set(v___x_1785_, 0, v___x_1816_);
v_m_1818_ = v___x_1785_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_a_1810_);
v_m_1818_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; double v___x_1821_; lean_object* v_data_1822_; 
v___x_1819_ = lean_box(v_result_1811_);
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
v___x_1821_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0);
lean_inc_ref(v_tag_1771_);
lean_inc_ref(v___x_1820_);
lean_inc(v_cls_1769_);
v_data_1822_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1822_, 0, v_cls_1769_);
lean_ctor_set(v_data_1822_, 1, v___x_1820_);
lean_ctor_set(v_data_1822_, 2, v_tag_1771_);
lean_ctor_set_float(v_data_1822_, sizeof(void*)*3, v___x_1821_);
lean_ctor_set_float(v_data_1822_, sizeof(void*)*3 + 8, v___x_1821_);
lean_ctor_set_uint8(v_data_1822_, sizeof(void*)*3 + 16, v_collapsed_1770_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v___x_1820_);
lean_dec(v_snd_1802_);
lean_dec(v_fst_1801_);
lean_dec_ref(v_tag_1771_);
lean_dec(v_cls_1769_);
v___y_1788_ = v_m_1818_;
v___y_1789_ = v___y_1809_;
v_data_1790_ = v_data_1822_;
goto v___jp_1787_;
}
else
{
lean_object* v_data_1823_; double v___x_1824_; double v___x_1825_; 
lean_dec_ref(v_data_1822_);
v_data_1823_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1823_, 0, v_cls_1769_);
lean_ctor_set(v_data_1823_, 1, v___x_1820_);
lean_ctor_set(v_data_1823_, 2, v_tag_1771_);
v___x_1824_ = lean_unbox_float(v_fst_1801_);
lean_dec(v_fst_1801_);
lean_ctor_set_float(v_data_1823_, sizeof(void*)*3, v___x_1824_);
v___x_1825_ = lean_unbox_float(v_snd_1802_);
lean_dec(v_snd_1802_);
lean_ctor_set_float(v_data_1823_, sizeof(void*)*3 + 8, v___x_1825_);
lean_ctor_set_uint8(v_data_1823_, sizeof(void*)*3 + 16, v_collapsed_1770_);
v___y_1788_ = v_m_1818_;
v___y_1789_ = v___y_1809_;
v_data_1790_ = v_data_1823_;
goto v___jp_1787_;
}
}
}
}
v___jp_1828_:
{
lean_object* v_ref_1829_; lean_object* v___x_1830_; 
v_ref_1829_ = lean_ctor_get(v___y_1779_, 5);
lean_inc(v___y_1780_);
lean_inc_ref(v___y_1779_);
lean_inc(v___y_1778_);
lean_inc_ref(v___y_1777_);
lean_inc(v_fst_1782_);
v___x_1830_ = lean_apply_6(v_msg_1775_, v_fst_1782_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, lean_box(0));
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
lean_inc(v_ref_1829_);
v___y_1809_ = v_ref_1829_;
v_a_1810_ = v_a_1831_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1832_; 
lean_dec_ref(v___x_1830_);
v___x_1832_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3);
lean_inc(v_ref_1829_);
v___y_1809_ = v_ref_1829_;
v_a_1810_ = v___x_1832_;
goto v___jp_1808_;
}
}
v___jp_1833_:
{
if (v_clsEnabled_1773_ == 0)
{
if (v___y_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v_traceState_1836_; lean_object* v_env_1837_; lean_object* v_nextMacroScope_1838_; lean_object* v_ngen_1839_; lean_object* v_auxDeclNGen_1840_; lean_object* v_cache_1841_; lean_object* v_messages_1842_; lean_object* v_infoState_1843_; lean_object* v_snapshotTasks_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1863_; 
lean_del_object(v___x_1804_);
lean_dec(v_snd_1802_);
lean_dec(v_fst_1801_);
lean_del_object(v___x_1785_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v_msg_1775_);
lean_dec_ref(v_tag_1771_);
lean_dec(v_cls_1769_);
v___x_1835_ = lean_st_ref_take(v___y_1780_);
v_traceState_1836_ = lean_ctor_get(v___x_1835_, 4);
v_env_1837_ = lean_ctor_get(v___x_1835_, 0);
v_nextMacroScope_1838_ = lean_ctor_get(v___x_1835_, 1);
v_ngen_1839_ = lean_ctor_get(v___x_1835_, 2);
v_auxDeclNGen_1840_ = lean_ctor_get(v___x_1835_, 3);
v_cache_1841_ = lean_ctor_get(v___x_1835_, 5);
v_messages_1842_ = lean_ctor_get(v___x_1835_, 6);
v_infoState_1843_ = lean_ctor_get(v___x_1835_, 7);
v_snapshotTasks_1844_ = lean_ctor_get(v___x_1835_, 8);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1846_ = v___x_1835_;
v_isShared_1847_ = v_isSharedCheck_1863_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snapshotTasks_1844_);
lean_inc(v_infoState_1843_);
lean_inc(v_messages_1842_);
lean_inc(v_cache_1841_);
lean_inc(v_traceState_1836_);
lean_inc(v_auxDeclNGen_1840_);
lean_inc(v_ngen_1839_);
lean_inc(v_nextMacroScope_1838_);
lean_inc(v_env_1837_);
lean_dec(v___x_1835_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1863_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint64_t v_tid_1848_; lean_object* v_traces_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1862_; 
v_tid_1848_ = lean_ctor_get_uint64(v_traceState_1836_, sizeof(void*)*1);
v_traces_1849_ = lean_ctor_get(v_traceState_1836_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_traceState_1836_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1851_ = v_traceState_1836_;
v_isShared_1852_ = v_isSharedCheck_1862_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_traces_1849_);
lean_dec(v_traceState_1836_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1862_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1774_, v_traces_1849_);
lean_dec_ref(v_traces_1849_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1853_);
lean_ctor_set_uint64(v_reuseFailAlloc_1861_, sizeof(void*)*1, v_tid_1848_);
v___x_1855_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1857_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 4, v___x_1855_);
v___x_1857_ = v___x_1846_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_env_1837_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_nextMacroScope_1838_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_ngen_1839_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_auxDeclNGen_1840_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1860_, 5, v_cache_1841_);
lean_ctor_set(v_reuseFailAlloc_1860_, 6, v_messages_1842_);
lean_ctor_set(v_reuseFailAlloc_1860_, 7, v_infoState_1843_);
lean_ctor_set(v_reuseFailAlloc_1860_, 8, v_snapshotTasks_1844_);
v___x_1857_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_st_ref_set(v___y_1780_, v___x_1857_);
lean_dec(v___y_1780_);
v___x_1859_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_fst_1782_);
return v___x_1859_;
}
}
}
}
}
else
{
goto v___jp_1828_;
}
}
else
{
goto v___jp_1828_;
}
}
v___jp_1864_:
{
double v___x_1866_; double v___x_1867_; double v___x_1868_; uint8_t v___x_1869_; 
v___x_1866_ = lean_unbox_float(v_snd_1802_);
v___x_1867_ = lean_unbox_float(v_fst_1801_);
v___x_1868_ = lean_float_sub(v___x_1866_, v___x_1867_);
v___x_1869_ = lean_float_decLt(v___y_1865_, v___x_1868_);
v___y_1834_ = v___x_1869_;
goto v___jp_1833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1882_, lean_object* v_collapsed_1883_, lean_object* v_tag_1884_, lean_object* v_opts_1885_, lean_object* v_clsEnabled_1886_, lean_object* v_oldTraces_1887_, lean_object* v_msg_1888_, lean_object* v_resStartStop_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
uint8_t v_collapsed_boxed_1895_; uint8_t v_clsEnabled_boxed_1896_; lean_object* v_res_1897_; 
v_collapsed_boxed_1895_ = lean_unbox(v_collapsed_1883_);
v_clsEnabled_boxed_1896_ = lean_unbox(v_clsEnabled_1886_);
v_res_1897_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1882_, v_collapsed_boxed_1895_, v_tag_1884_, v_opts_1885_, v_clsEnabled_boxed_1896_, v_oldTraces_1887_, v_msg_1888_, v_resStartStop_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec_ref(v_opts_1885_);
return v_res_1897_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1898_; double v___x_1899_; 
v___x_1898_ = lean_unsigned_to_nat(1000000000u);
v___x_1899_ = lean_float_of_nat(v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1900_, lean_object* v_numIndParams_1901_, lean_object* v_positions_1902_, lean_object* v_fnIndex_1903_, lean_object* v_recArg_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_options_1910_; uint8_t v_hasTrace_1911_; lean_object* v___x_1912_; lean_object* v___f_1913_; 
v_options_1910_ = lean_ctor_get(v_a_1907_, 2);
v_hasTrace_1911_ = lean_ctor_get_uint8(v_options_1910_, sizeof(void*)*1);
v___x_1912_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1900_);
lean_inc_ref(v_recArg_1904_);
v___f_1913_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1913_, 0, v___x_1912_);
lean_closure_set(v___f_1913_, 1, v_fnIndex_1903_);
lean_closure_set(v___f_1913_, 2, v_recArg_1904_);
lean_closure_set(v___f_1913_, 3, v_below_1900_);
if (v_hasTrace_1911_ == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref(v_recArg_1904_);
v___x_1914_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1900_, v_numIndParams_1901_, v_positions_1902_, v___f_1913_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1914_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v_a_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v_a_1923_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v_a_1939_; uint8_t v___x_1990_; 
v___x_1915_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1916_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(v___x_1915_, v_a_1907_);
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
lean_inc_ref(v_below_1900_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1918_, 0, v_below_1900_);
lean_closure_set(v___f_1918_, 1, v_recArg_1904_);
v___x_1919_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__1));
v___x_1990_ = lean_unbox(v_a_1917_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = l_Lean_trace_profiler;
v___x_1992_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1910_, v___x_1991_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
lean_dec_ref(v___f_1918_);
lean_dec(v_a_1917_);
v___x_1993_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1900_, v_numIndParams_1901_, v_positions_1902_, v___f_1913_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1993_;
}
else
{
lean_inc_ref(v_options_1910_);
goto v___jp_1949_;
}
}
else
{
lean_inc_ref(v_options_1910_);
goto v___jp_1949_;
}
v___jp_1920_:
{
lean_object* v___x_1924_; double v___x_1925_; double v___x_1926_; double v___x_1927_; double v___x_1928_; double v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1924_ = lean_io_mono_nanos_now();
v___x_1925_ = lean_float_of_nat(v___y_1921_);
v___x_1926_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1927_ = lean_float_div(v___x_1925_, v___x_1926_);
v___x_1928_ = lean_float_of_nat(v___x_1924_);
v___x_1929_ = lean_float_div(v___x_1928_, v___x_1926_);
v___x_1930_ = lean_box_float(v___x_1927_);
v___x_1931_ = lean_box_float(v___x_1929_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_a_1923_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_unbox(v_a_1917_);
lean_dec(v_a_1917_);
v___x_1935_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1915_, v_hasTrace_1911_, v___x_1919_, v_options_1910_, v___x_1934_, v___y_1922_, v___f_1918_, v___x_1933_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec_ref(v_options_1910_);
return v___x_1935_;
}
v___jp_1936_:
{
lean_object* v___x_1940_; double v___x_1941_; double v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1940_ = lean_io_get_num_heartbeats();
v___x_1941_ = lean_float_of_nat(v___y_1937_);
v___x_1942_ = lean_float_of_nat(v___x_1940_);
v___x_1943_ = lean_box_float(v___x_1941_);
v___x_1944_ = lean_box_float(v___x_1942_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v_a_1939_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = lean_unbox(v_a_1917_);
lean_dec(v_a_1917_);
v___x_1948_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1915_, v_hasTrace_1911_, v___x_1919_, v_options_1910_, v___x_1947_, v___y_1938_, v___f_1918_, v___x_1946_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec_ref(v_options_1910_);
return v___x_1948_;
}
v___jp_1949_:
{
lean_object* v___x_1950_; lean_object* v_a_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1950_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1908_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1950_);
v___x_1952_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1953_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1910_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_io_mono_nanos_now();
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
v___x_1955_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1900_, v_numIndParams_1901_, v_positions_1902_, v___f_1913_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 1);
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
v___y_1921_ = v___x_1954_;
v___y_1922_ = v_a_1951_;
v_a_1923_ = v___x_1961_;
goto v___jp_1920_;
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_a_1964_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1955_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1955_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 0);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
v___y_1921_ = v___x_1954_;
v___y_1922_ = v_a_1951_;
v_a_1923_ = v___x_1969_;
goto v___jp_1920_;
}
}
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
v___x_1973_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1900_, v_numIndParams_1901_, v_positions_1902_, v___f_1913_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set_tag(v___x_1976_, 1);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
v___y_1937_ = v___x_1972_;
v___y_1938_ = v_a_1951_;
v_a_1939_ = v___x_1979_;
goto v___jp_1936_;
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v_a_1982_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1973_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1973_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 0);
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
v___y_1937_ = v___x_1972_;
v___y_1938_ = v_a_1951_;
v_a_1939_ = v___x_1987_;
goto v___jp_1936_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1994_, lean_object* v_numIndParams_1995_, lean_object* v_positions_1996_, lean_object* v_fnIndex_1997_, lean_object* v_recArg_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_Elab_Structural_toBelow(v_below_1994_, v_numIndParams_1995_, v_positions_1996_, v_fnIndex_1997_, v_recArg_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_00_u03b1_2005_, lean_object* v_x_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_x_2006_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2013_, lean_object* v_x_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_00_u03b1_2013_, v_x_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v_b_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_apply_8(v_k_2021_, v_b_2024_, v___y_2022_, v___y_2023_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, lean_box(0));
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v_b_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_2031_, v___y_2032_, v___y_2033_, v_b_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_2041_, uint8_t v_bi_2042_, lean_object* v_type_2043_, lean_object* v_k_2044_, uint8_t v_kind_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___f_2053_; lean_object* v___x_2054_; 
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2053_, 0, v_k_2044_);
lean_closure_set(v___f_2053_, 1, v___y_2046_);
lean_closure_set(v___f_2053_, 2, v___y_2047_);
v___x_2054_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2041_, v_bi_2042_, v_type_2043_, v___f_2053_, v_kind_2045_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2054_) == 0)
{
return v___x_2054_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_2063_, lean_object* v_bi_2064_, lean_object* v_type_2065_, lean_object* v_k_2066_, lean_object* v_kind_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
uint8_t v_bi_boxed_2075_; uint8_t v_kind_boxed_2076_; lean_object* v_res_2077_; 
v_bi_boxed_2075_ = lean_unbox(v_bi_2064_);
v_kind_boxed_2076_ = lean_unbox(v_kind_2067_);
v_res_2077_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2063_, v_bi_boxed_2075_, v_type_2065_, v_k_2066_, v_kind_boxed_2076_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2078_, lean_object* v_name_2079_, uint8_t v_bi_2080_, lean_object* v_type_2081_, lean_object* v_k_2082_, uint8_t v_kind_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2079_, v_bi_2080_, v_type_2081_, v_k_2082_, v_kind_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2092_, lean_object* v_name_2093_, lean_object* v_bi_2094_, lean_object* v_type_2095_, lean_object* v_k_2096_, lean_object* v_kind_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
uint8_t v_bi_boxed_2105_; uint8_t v_kind_boxed_2106_; lean_object* v_res_2107_; 
v_bi_boxed_2105_ = lean_unbox(v_bi_2094_);
v_kind_boxed_2106_ = lean_unbox(v_kind_2097_);
v_res_2107_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2092_, v_name_2093_, v_bi_boxed_2105_, v_type_2095_, v_k_2096_, v_kind_boxed_2106_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(lean_object* v_cls_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_options_2111_; uint8_t v_hasTrace_2112_; 
v_options_2111_ = lean_ctor_get(v___y_2109_, 2);
v_hasTrace_2112_ = lean_ctor_get_uint8(v_options_2111_, sizeof(void*)*1);
if (v_hasTrace_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec(v_cls_2108_);
v___x_2113_ = lean_box(v_hasTrace_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
else
{
lean_object* v_inheritedTraceOptions_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_inheritedTraceOptions_2115_ = lean_ctor_get(v___y_2109_, 13);
v___x_2116_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__1));
v___x_2117_ = l_Lean_Name_append(v___x_2116_, v_cls_2108_);
v___x_2118_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2115_, v_options_2111_, v___x_2117_);
lean_dec(v___x_2117_);
v___x_2119_ = lean_box(v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_cls_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v_cls_2121_, v___y_2122_);
lean_dec_ref(v___y_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_cls_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v_cls_2125_, v___y_2130_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___boxed(lean_object* v_cls_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v_cls_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0(lean_object* v_k_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v_b_2146_, lean_object* v_c_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_apply_9(v_k_2143_, v_b_2146_, v_c_2147_, v___y_2144_, v___y_2145_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, lean_box(0));
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0___boxed(lean_object* v_k_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v_b_2157_, lean_object* v_c_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0(v_k_2154_, v___y_2155_, v___y_2156_, v_b_2157_, v_c_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(lean_object* v_e_2165_, lean_object* v_maxFVars_2166_, lean_object* v_k_2167_, uint8_t v_cleanupAnnotations_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___f_2176_; uint8_t v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___f_2176_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2176_, 0, v_k_2167_);
lean_closure_set(v___f_2176_, 1, v___y_2169_);
lean_closure_set(v___f_2176_, 2, v___y_2170_);
v___x_2177_ = 1;
v___x_2178_ = 0;
v___x_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_maxFVars_2166_);
v___x_2180_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2165_, v___x_2177_, v___x_2178_, v___x_2177_, v___x_2178_, v___x_2179_, v___f_2176_, v_cleanupAnnotations_2168_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec_ref(v___x_2179_);
if (lean_obj_tag(v___x_2180_) == 0)
{
return v___x_2180_;
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___boxed(lean_object* v_e_2189_, lean_object* v_maxFVars_2190_, lean_object* v_k_2191_, lean_object* v_cleanupAnnotations_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2200_; lean_object* v_res_2201_; 
v_cleanupAnnotations_boxed_2200_ = lean_unbox(v_cleanupAnnotations_2192_);
v_res_2201_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(v_e_2189_, v_maxFVars_2190_, v_k_2191_, v_cleanupAnnotations_boxed_2200_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_00_u03b1_2202_, lean_object* v_e_2203_, lean_object* v_maxFVars_2204_, lean_object* v_k_2205_, uint8_t v_cleanupAnnotations_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(v_e_2203_, v_maxFVars_2204_, v_k_2205_, v_cleanupAnnotations_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_00_u03b1_2215_, lean_object* v_e_2216_, lean_object* v_maxFVars_2217_, lean_object* v_k_2218_, lean_object* v_cleanupAnnotations_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2227_; lean_object* v_res_2228_; 
v_cleanupAnnotations_boxed_2227_ = lean_unbox(v_cleanupAnnotations_2219_);
v_res_2228_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_00_u03b1_2215_, v_e_2216_, v_maxFVars_2217_, v_k_2218_, v_cleanupAnnotations_boxed_2227_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_cls_2229_, lean_object* v_msg_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_ref_2236_; lean_object* v___x_2237_; lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2282_; 
v_ref_2236_ = lean_ctor_get(v___y_2233_, 5);
v___x_2237_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2282_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2282_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v_traceState_2243_; lean_object* v_env_2244_; lean_object* v_nextMacroScope_2245_; lean_object* v_ngen_2246_; lean_object* v_auxDeclNGen_2247_; lean_object* v_cache_2248_; lean_object* v_messages_2249_; lean_object* v_infoState_2250_; lean_object* v_snapshotTasks_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2281_; 
v___x_2242_ = lean_st_ref_take(v___y_2234_);
v_traceState_2243_ = lean_ctor_get(v___x_2242_, 4);
v_env_2244_ = lean_ctor_get(v___x_2242_, 0);
v_nextMacroScope_2245_ = lean_ctor_get(v___x_2242_, 1);
v_ngen_2246_ = lean_ctor_get(v___x_2242_, 2);
v_auxDeclNGen_2247_ = lean_ctor_get(v___x_2242_, 3);
v_cache_2248_ = lean_ctor_get(v___x_2242_, 5);
v_messages_2249_ = lean_ctor_get(v___x_2242_, 6);
v_infoState_2250_ = lean_ctor_get(v___x_2242_, 7);
v_snapshotTasks_2251_ = lean_ctor_get(v___x_2242_, 8);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2253_ = v___x_2242_;
v_isShared_2254_ = v_isSharedCheck_2281_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_snapshotTasks_2251_);
lean_inc(v_infoState_2250_);
lean_inc(v_messages_2249_);
lean_inc(v_cache_2248_);
lean_inc(v_traceState_2243_);
lean_inc(v_auxDeclNGen_2247_);
lean_inc(v_ngen_2246_);
lean_inc(v_nextMacroScope_2245_);
lean_inc(v_env_2244_);
lean_dec(v___x_2242_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2281_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
uint64_t v_tid_2255_; lean_object* v_traces_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2280_; 
v_tid_2255_ = lean_ctor_get_uint64(v_traceState_2243_, sizeof(void*)*1);
v_traces_2256_ = lean_ctor_get(v_traceState_2243_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_traceState_2243_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2258_ = v_traceState_2243_;
v_isShared_2259_ = v_isSharedCheck_2280_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_traces_2256_);
lean_dec(v_traceState_2243_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2280_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; double v___x_2261_; uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2260_ = lean_box(0);
v___x_2261_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0);
v___x_2262_ = 0;
v___x_2263_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__1));
v___x_2264_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2264_, 0, v_cls_2229_);
lean_ctor_set(v___x_2264_, 1, v___x_2260_);
lean_ctor_set(v___x_2264_, 2, v___x_2263_);
lean_ctor_set_float(v___x_2264_, sizeof(void*)*3, v___x_2261_);
lean_ctor_set_float(v___x_2264_, sizeof(void*)*3 + 8, v___x_2261_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*3 + 16, v___x_2262_);
v___x_2265_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__2));
v___x_2266_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v_a_2238_);
lean_ctor_set(v___x_2266_, 2, v___x_2265_);
lean_inc(v_ref_2236_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_ref_2236_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = l_Lean_PersistentArray_push___redArg(v_traces_2256_, v___x_2267_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2268_);
v___x_2270_ = v___x_2258_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2268_);
lean_ctor_set_uint64(v_reuseFailAlloc_2279_, sizeof(void*)*1, v_tid_2255_);
v___x_2270_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 4, v___x_2270_);
v___x_2272_ = v___x_2253_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_env_2244_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_nextMacroScope_2245_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v_ngen_2246_);
lean_ctor_set(v_reuseFailAlloc_2278_, 3, v_auxDeclNGen_2247_);
lean_ctor_set(v_reuseFailAlloc_2278_, 4, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2278_, 5, v_cache_2248_);
lean_ctor_set(v_reuseFailAlloc_2278_, 6, v_messages_2249_);
lean_ctor_set(v_reuseFailAlloc_2278_, 7, v_infoState_2250_);
lean_ctor_set(v_reuseFailAlloc_2278_, 8, v_snapshotTasks_2251_);
v___x_2272_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = lean_st_ref_set(v___y_2234_, v___x_2272_);
v___x_2274_ = lean_box(0);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2274_);
v___x_2276_ = v___x_2240_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_cls_2283_, lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_cls_2283_, v_msg_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2291_, lean_object* v_as_2292_, size_t v_i_2293_, size_t v_stop_2294_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_usize_dec_eq(v_i_2293_, v_stop_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v_fnName_2297_; lean_object* v_recArgPos_2298_; uint8_t v___x_2299_; 
v___x_2296_ = lean_array_uget_borrowed(v_as_2292_, v_i_2293_);
v_fnName_2297_ = lean_ctor_get(v___x_2296_, 0);
v_recArgPos_2298_ = lean_ctor_get(v___x_2296_, 2);
lean_inc(v_recArgPos_2298_);
lean_inc(v_fnName_2297_);
v___x_2299_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2297_, v_recArgPos_2298_, v_e_2291_);
if (v___x_2299_ == 0)
{
size_t v___x_2300_; size_t v___x_2301_; 
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2293_, v___x_2300_);
v_i_2293_ = v___x_2301_;
goto _start;
}
else
{
return v___x_2299_;
}
}
else
{
uint8_t v___x_2303_; 
v___x_2303_ = 0;
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2304_, lean_object* v_as_2305_, lean_object* v_i_2306_, lean_object* v_stop_2307_){
_start:
{
size_t v_i_boxed_2308_; size_t v_stop_boxed_2309_; uint8_t v_res_2310_; lean_object* v_r_2311_; 
v_i_boxed_2308_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_stop_boxed_2309_ = lean_unbox_usize(v_stop_2307_);
lean_dec(v_stop_2307_);
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2304_, v_as_2305_, v_i_boxed_2308_, v_stop_boxed_2309_);
lean_dec_ref(v_as_2305_);
lean_dec_ref(v_e_2304_);
v_r_2311_ = lean_box(v_res_2310_);
return v_r_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v_env_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2315_ = lean_st_ref_get(v___y_2313_);
v_env_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc_ref(v_env_2316_);
lean_dec(v___x_2315_);
v___x_2317_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2316_, v_declName_2312_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2319_, v___y_2320_);
lean_dec(v___y_2320_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; lean_object* v_toApplicative_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2395_; 
v___x_2331_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v___x_2331_, 1);
lean_dec(v_unused_2396_);
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2395_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_toApplicative_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2395_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v_toFunctor_2336_; lean_object* v_toSeq_2337_; lean_object* v_toSeqLeft_2338_; lean_object* v_toSeqRight_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2393_; 
v_toFunctor_2336_ = lean_ctor_get(v_toApplicative_2332_, 0);
v_toSeq_2337_ = lean_ctor_get(v_toApplicative_2332_, 2);
v_toSeqLeft_2338_ = lean_ctor_get(v_toApplicative_2332_, 3);
v_toSeqRight_2339_ = lean_ctor_get(v_toApplicative_2332_, 4);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_toApplicative_2332_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v_toApplicative_2332_, 1);
lean_dec(v_unused_2394_);
v___x_2341_ = v_toApplicative_2332_;
v_isShared_2342_ = v_isSharedCheck_2393_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_toSeqRight_2339_);
lean_inc(v_toSeqLeft_2338_);
lean_inc(v_toSeq_2337_);
lean_inc(v_toFunctor_2336_);
lean_dec(v_toApplicative_2332_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2393_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___f_2343_; lean_object* v___f_2344_; lean_object* v___f_2345_; lean_object* v___f_2346_; lean_object* v___x_2347_; lean_object* v___f_2348_; lean_object* v___f_2349_; lean_object* v___f_2350_; lean_object* v___x_2352_; 
v___f_2343_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2344_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref(v_toFunctor_2336_);
v___f_2345_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2345_, 0, v_toFunctor_2336_);
v___f_2346_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2346_, 0, v_toFunctor_2336_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___f_2345_);
lean_ctor_set(v___x_2347_, 1, v___f_2346_);
v___f_2348_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2348_, 0, v_toSeqRight_2339_);
v___f_2349_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2349_, 0, v_toSeqLeft_2338_);
v___f_2350_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2350_, 0, v_toSeq_2337_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 4, v___f_2348_);
lean_ctor_set(v___x_2341_, 3, v___f_2349_);
lean_ctor_set(v___x_2341_, 2, v___f_2350_);
lean_ctor_set(v___x_2341_, 1, v___f_2343_);
lean_ctor_set(v___x_2341_, 0, v___x_2347_);
v___x_2352_ = v___x_2341_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___f_2343_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v___f_2350_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v___f_2349_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v___f_2348_);
v___x_2352_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 1, v___f_2344_);
lean_ctor_set(v___x_2334_, 0, v___x_2352_);
v___x_2354_ = v___x_2334_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v___f_2344_);
v___x_2354_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; lean_object* v_toApplicative_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2389_; 
v___x_2355_ = l_ReaderT_instMonad___redArg(v___x_2354_);
v_toApplicative_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2355_, 1);
lean_dec(v_unused_2390_);
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2389_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_toApplicative_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2389_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v_toFunctor_2360_; lean_object* v_toSeq_2361_; lean_object* v_toSeqLeft_2362_; lean_object* v_toSeqRight_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2387_; 
v_toFunctor_2360_ = lean_ctor_get(v_toApplicative_2356_, 0);
v_toSeq_2361_ = lean_ctor_get(v_toApplicative_2356_, 2);
v_toSeqLeft_2362_ = lean_ctor_get(v_toApplicative_2356_, 3);
v_toSeqRight_2363_ = lean_ctor_get(v_toApplicative_2356_, 4);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_toApplicative_2356_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; 
v_unused_2388_ = lean_ctor_get(v_toApplicative_2356_, 1);
lean_dec(v_unused_2388_);
v___x_2365_ = v_toApplicative_2356_;
v_isShared_2366_ = v_isSharedCheck_2387_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_toSeqRight_2363_);
lean_inc(v_toSeqLeft_2362_);
lean_inc(v_toSeq_2361_);
lean_inc(v_toFunctor_2360_);
lean_dec(v_toApplicative_2356_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2387_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___f_2367_; lean_object* v___f_2368_; lean_object* v___f_2369_; lean_object* v___f_2370_; lean_object* v___x_2371_; lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___x_2376_; 
v___f_2367_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2368_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2360_);
v___f_2369_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2369_, 0, v_toFunctor_2360_);
v___f_2370_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2370_, 0, v_toFunctor_2360_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___f_2369_);
lean_ctor_set(v___x_2371_, 1, v___f_2370_);
v___f_2372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2372_, 0, v_toSeqRight_2363_);
v___f_2373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2373_, 0, v_toSeqLeft_2362_);
v___f_2374_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2374_, 0, v_toSeq_2361_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 4, v___f_2372_);
lean_ctor_set(v___x_2365_, 3, v___f_2373_);
lean_ctor_set(v___x_2365_, 2, v___f_2374_);
lean_ctor_set(v___x_2365_, 1, v___f_2367_);
lean_ctor_set(v___x_2365_, 0, v___x_2371_);
v___x_2376_ = v___x_2365_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v___f_2367_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v___f_2374_);
lean_ctor_set(v_reuseFailAlloc_2386_, 3, v___f_2373_);
lean_ctor_set(v_reuseFailAlloc_2386_, 4, v___f_2372_);
v___x_2376_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 1, v___f_2368_);
lean_ctor_set(v___x_2358_, 0, v___x_2376_);
v___x_2378_ = v___x_2358_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v___f_2368_);
v___x_2378_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_42662__overap_2383_; lean_object* v___x_2384_; 
v___x_2379_ = l_ReaderT_instMonad___redArg(v___x_2378_);
v___x_2380_ = l_ReaderT_instMonad___redArg(v___x_2379_);
v___x_2381_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2382_ = l_instInhabitedOfMonad___redArg(v___x_2380_, v___x_2381_);
v___x_42662__overap_2383_ = lean_panic_fn(v___x_2382_, v_msg_2323_);
v___x_2384_ = lean_apply_7(v___x_42662__overap_2383_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, lean_box(0));
return v___x_2384_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
return v_res_2405_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
lean_ctor_set(v___x_2411_, 2, v___x_2410_);
lean_ctor_set(v___x_2411_, 3, v___x_2409_);
lean_ctor_set(v___x_2411_, 4, v___x_2409_);
lean_ctor_set(v___x_2411_, 5, v___x_2409_);
lean_ctor_set(v___x_2411_, 6, v___x_2409_);
lean_ctor_set(v___x_2411_, 7, v___x_2409_);
lean_ctor_set(v___x_2411_, 8, v___x_2409_);
return v___x_2411_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_unsigned_to_nat(32u);
v___x_2413_ = lean_mk_empty_array_with_capacity(v___x_2412_);
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2415_ = ((size_t)5ULL);
v___x_2416_ = lean_unsigned_to_nat(0u);
v___x_2417_ = lean_unsigned_to_nat(32u);
v___x_2418_ = lean_mk_empty_array_with_capacity(v___x_2417_);
v___x_2419_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_2420_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___x_2418_);
lean_ctor_set(v___x_2420_, 2, v___x_2416_);
lean_ctor_set(v___x_2420_, 3, v___x_2416_);
lean_ctor_set_usize(v___x_2420_, 4, v___x_2415_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = lean_box(1);
v___x_2422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_2423_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_2424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
lean_ctor_set(v___x_2424_, 2, v___x_2421_);
return v___x_2424_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_2427_ = l_Lean_stringToMessageData(v___x_2426_);
return v___x_2427_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_2430_ = l_Lean_stringToMessageData(v___x_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_2433_ = l_Lean_stringToMessageData(v___x_2432_);
return v___x_2433_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_2436_ = l_Lean_stringToMessageData(v___x_2435_);
return v___x_2436_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__14));
v___x_2439_ = l_Lean_stringToMessageData(v___x_2438_);
return v___x_2439_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__16));
v___x_2442_ = l_Lean_stringToMessageData(v___x_2441_);
return v___x_2442_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__18));
v___x_2445_ = l_Lean_stringToMessageData(v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_2446_, lean_object* v_declHint_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; lean_object* v_env_2451_; uint8_t v___x_2452_; 
v___x_2450_ = lean_st_ref_get(v___y_2448_);
v_env_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc_ref(v_env_2451_);
lean_dec(v___x_2450_);
v___x_2452_ = l_Lean_Name_isAnonymous(v_declHint_2447_);
if (v___x_2452_ == 0)
{
uint8_t v_isExporting_2453_; 
v_isExporting_2453_ = lean_ctor_get_uint8(v_env_2451_, sizeof(void*)*8);
if (v_isExporting_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec_ref(v_env_2451_);
lean_dec(v_declHint_2447_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v_msg_2446_);
return v___x_2454_;
}
else
{
lean_object* v___x_2455_; uint8_t v___x_2456_; 
lean_inc_ref(v_env_2451_);
v___x_2455_ = l_Lean_Environment_setExporting(v_env_2451_, v___x_2452_);
lean_inc(v_declHint_2447_);
lean_inc_ref(v___x_2455_);
v___x_2456_ = l_Lean_Environment_contains(v___x_2455_, v_declHint_2447_, v_isExporting_2453_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; 
lean_dec_ref(v___x_2455_);
lean_dec_ref(v_env_2451_);
lean_dec(v_declHint_2447_);
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_msg_2446_);
return v___x_2457_;
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v_c_2463_; lean_object* v___x_2464_; 
v___x_2458_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_2459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_2460_ = l_Lean_Options_empty;
v___x_2461_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2455_);
lean_ctor_set(v___x_2461_, 1, v___x_2458_);
lean_ctor_set(v___x_2461_, 2, v___x_2459_);
lean_ctor_set(v___x_2461_, 3, v___x_2460_);
lean_inc(v_declHint_2447_);
v___x_2462_ = l_Lean_MessageData_ofConstName(v_declHint_2447_, v___x_2452_);
v_c_2463_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2463_, 0, v___x_2461_);
lean_ctor_set(v_c_2463_, 1, v___x_2462_);
v___x_2464_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2451_, v_declHint_2447_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_dec_ref(v_env_2451_);
lean_dec(v_declHint_2447_);
v___x_2465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v_c_2463_);
v___x_2467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_2468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = l_Lean_MessageData_note(v___x_2468_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_msg_2446_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
else
{
lean_object* v_val_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2507_; 
v_val_2472_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2474_ = v___x_2464_;
v_isShared_2475_ = v_isSharedCheck_2507_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_val_2472_);
lean_dec(v___x_2464_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2507_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_mod_2479_; uint8_t v___x_2480_; 
v___x_2476_ = lean_box(0);
v___x_2477_ = l_Lean_Environment_header(v_env_2451_);
lean_dec_ref(v_env_2451_);
v___x_2478_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2477_);
v_mod_2479_ = lean_array_get(v___x_2476_, v___x_2478_, v_val_2472_);
lean_dec(v_val_2472_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = l_Lean_isPrivateName(v_declHint_2447_);
lean_dec(v_declHint_2447_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v_c_2463_);
v___x_2483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_2484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2482_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = l_Lean_MessageData_ofName(v_mod_2479_);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_MessageData_note(v___x_2488_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v_msg_2446_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2490_);
v___x_2492_ = v___x_2474_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2494_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_2495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v_c_2463_);
v___x_2496_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17);
v___x_2497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Lean_MessageData_ofName(v_mod_2479_);
v___x_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_MessageData_note(v___x_2501_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_msg_2446_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2503_);
v___x_2505_ = v___x_2474_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2508_; 
lean_dec_ref(v_env_2451_);
lean_dec(v_declHint_2447_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_msg_2446_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_2509_, lean_object* v_declHint_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_2509_, v_declHint_2510_, v___y_2511_);
lean_dec(v___y_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19(lean_object* v_msg_2514_, lean_object* v_declHint_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2533_; 
v___x_2523_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_2514_, v_declHint_2515_, v___y_2521_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2528_ = l_Lean_unknownIdentifierMessageTag;
v___x_2529_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v_a_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2529_);
v___x_2531_ = v___x_2526_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_2534_, lean_object* v_declHint_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19(v_msg_2534_, v_declHint_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec(v___y_2536_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_ref_2550_; lean_object* v___x_2551_; lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2560_; 
v_ref_2550_ = lean_ctor_get(v___y_2547_, 5);
v___x_2551_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2560_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2560_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
lean_inc(v_ref_2550_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v_ref_2550_);
lean_ctor_set(v___x_2556_, 1, v_a_2552_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set_tag(v___x_2554_, 1);
lean_ctor_set(v___x_2554_, 0, v___x_2556_);
v___x_2558_ = v___x_2554_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_2568_, lean_object* v_msg_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_fileName_2577_; lean_object* v_fileMap_2578_; lean_object* v_options_2579_; lean_object* v_currRecDepth_2580_; lean_object* v_maxRecDepth_2581_; lean_object* v_ref_2582_; lean_object* v_currNamespace_2583_; lean_object* v_openDecls_2584_; lean_object* v_initHeartbeats_2585_; lean_object* v_maxHeartbeats_2586_; lean_object* v_quotContext_2587_; lean_object* v_currMacroScope_2588_; uint8_t v_diag_2589_; lean_object* v_cancelTk_x3f_2590_; uint8_t v_suppressElabErrors_2591_; lean_object* v_inheritedTraceOptions_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2601_; 
v_fileName_2577_ = lean_ctor_get(v___y_2574_, 0);
v_fileMap_2578_ = lean_ctor_get(v___y_2574_, 1);
v_options_2579_ = lean_ctor_get(v___y_2574_, 2);
v_currRecDepth_2580_ = lean_ctor_get(v___y_2574_, 3);
v_maxRecDepth_2581_ = lean_ctor_get(v___y_2574_, 4);
v_ref_2582_ = lean_ctor_get(v___y_2574_, 5);
v_currNamespace_2583_ = lean_ctor_get(v___y_2574_, 6);
v_openDecls_2584_ = lean_ctor_get(v___y_2574_, 7);
v_initHeartbeats_2585_ = lean_ctor_get(v___y_2574_, 8);
v_maxHeartbeats_2586_ = lean_ctor_get(v___y_2574_, 9);
v_quotContext_2587_ = lean_ctor_get(v___y_2574_, 10);
v_currMacroScope_2588_ = lean_ctor_get(v___y_2574_, 11);
v_diag_2589_ = lean_ctor_get_uint8(v___y_2574_, sizeof(void*)*14);
v_cancelTk_x3f_2590_ = lean_ctor_get(v___y_2574_, 12);
v_suppressElabErrors_2591_ = lean_ctor_get_uint8(v___y_2574_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2592_ = lean_ctor_get(v___y_2574_, 13);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___y_2574_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2594_ = v___y_2574_;
v_isShared_2595_ = v_isSharedCheck_2601_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_inheritedTraceOptions_2592_);
lean_inc(v_cancelTk_x3f_2590_);
lean_inc(v_currMacroScope_2588_);
lean_inc(v_quotContext_2587_);
lean_inc(v_maxHeartbeats_2586_);
lean_inc(v_initHeartbeats_2585_);
lean_inc(v_openDecls_2584_);
lean_inc(v_currNamespace_2583_);
lean_inc(v_ref_2582_);
lean_inc(v_maxRecDepth_2581_);
lean_inc(v_currRecDepth_2580_);
lean_inc(v_options_2579_);
lean_inc(v_fileMap_2578_);
lean_inc(v_fileName_2577_);
lean_dec(v___y_2574_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2601_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_ref_2596_; lean_object* v___x_2598_; 
v_ref_2596_ = l_Lean_replaceRef(v_ref_2568_, v_ref_2582_);
lean_dec(v_ref_2582_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 5, v_ref_2596_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_fileName_2577_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_fileMap_2578_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_options_2579_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_currRecDepth_2580_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_maxRecDepth_2581_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v_ref_2596_);
lean_ctor_set(v_reuseFailAlloc_2600_, 6, v_currNamespace_2583_);
lean_ctor_set(v_reuseFailAlloc_2600_, 7, v_openDecls_2584_);
lean_ctor_set(v_reuseFailAlloc_2600_, 8, v_initHeartbeats_2585_);
lean_ctor_set(v_reuseFailAlloc_2600_, 9, v_maxHeartbeats_2586_);
lean_ctor_set(v_reuseFailAlloc_2600_, 10, v_quotContext_2587_);
lean_ctor_set(v_reuseFailAlloc_2600_, 11, v_currMacroScope_2588_);
lean_ctor_set(v_reuseFailAlloc_2600_, 12, v_cancelTk_x3f_2590_);
lean_ctor_set(v_reuseFailAlloc_2600_, 13, v_inheritedTraceOptions_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*14, v_diag_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*14 + 1, v_suppressElabErrors_2591_);
v___x_2598_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2569_, v___y_2572_, v___y_2573_, v___x_2598_, v___y_2575_);
lean_dec_ref(v___x_2598_);
return v___x_2599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_2602_, lean_object* v_msg_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(v_ref_2602_, v_msg_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec(v_ref_2602_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(lean_object* v_ref_2612_, lean_object* v_msg_2613_, lean_object* v_declHint_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; lean_object* v_a_2623_; lean_object* v___x_2624_; 
v___x_2622_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19(v_msg_2613_, v_declHint_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref(v___x_2622_);
v___x_2624_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(v_ref_2612_, v_a_2623_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg___boxed(lean_object* v_ref_2625_, lean_object* v_msg_2626_, lean_object* v_declHint_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(v_ref_2625_, v_msg_2626_, v_declHint_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v_ref_2625_);
return v_res_2635_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__0));
v___x_2638_ = l_Lean_stringToMessageData(v___x_2637_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__2));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(lean_object* v_ref_2642_, lean_object* v_constName_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; uint8_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2651_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1);
v___x_2652_ = 0;
lean_inc(v_constName_2643_);
v___x_2653_ = l_Lean_MessageData_ofConstName(v_constName_2643_, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2651_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2654_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(v_ref_2642_, v___x_2656_, v_constName_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___boxed(lean_object* v_ref_2658_, lean_object* v_constName_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(v_ref_2658_, v_constName_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec(v_ref_2658_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(lean_object* v_constName_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_ref_2676_; lean_object* v___x_2677_; 
v_ref_2676_ = lean_ctor_get(v___y_2673_, 5);
lean_inc(v_ref_2676_);
v___x_2677_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(v_ref_2676_, v_constName_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v_ref_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_constName_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(v_constName_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; lean_object* v_env_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; 
v___x_2695_ = lean_st_ref_get(v___y_2693_);
v_env_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc_ref(v_env_2696_);
lean_dec(v___x_2695_);
v___x_2697_ = 0;
lean_inc(v_constName_2687_);
v___x_2698_ = l_Lean_Environment_find_x3f(v_env_2696_, v_constName_2687_, v___x_2697_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(v_constName_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
return v___x_2699_;
}
else
{
lean_object* v_val_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec_ref(v___y_2692_);
lean_dec(v_constName_2687_);
v_val_2700_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2698_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_val_2700_);
lean_dec(v___x_2698_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set_tag(v___x_2702_, 0);
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_val_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
return v_res_2716_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2721_ = lean_unsigned_to_nat(53u);
v___x_2722_ = lean_unsigned_to_nat(62u);
v___x_2723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2725_ = l_mkPanicMessageWithDecl(v___x_2724_, v___x_2723_, v___x_2722_, v___x_2721_, v___x_2720_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2726_, size_t v_i_2727_, lean_object* v_bs_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
uint8_t v___x_2736_; 
v___x_2736_ = lean_usize_dec_lt(v_i_2727_, v_sz_2726_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; 
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v_bs_2728_);
return v___x_2737_;
}
else
{
lean_object* v_v_2738_; lean_object* v___x_2739_; 
v_v_2738_ = lean_array_uget_borrowed(v_bs_2728_, v_i_2727_);
lean_inc_ref(v___y_2733_);
lean_inc(v_v_2738_);
v___x_2739_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2738_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2741_; lean_object* v_bs_x27_2742_; lean_object* v_a_2744_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = lean_unsigned_to_nat(0u);
v_bs_x27_2742_ = lean_array_uset(v_bs_2728_, v_i_2727_, v___x_2741_);
if (lean_obj_tag(v_a_2740_) == 6)
{
lean_object* v_val_2749_; lean_object* v_numFields_2750_; uint8_t v___x_2751_; lean_object* v___x_2752_; 
v_val_2749_ = lean_ctor_get(v_a_2740_, 0);
lean_inc_ref(v_val_2749_);
lean_dec_ref(v_a_2740_);
v_numFields_2750_ = lean_ctor_get(v_val_2749_, 4);
lean_inc(v_numFields_2750_);
lean_dec_ref(v_val_2749_);
v___x_2751_ = 0;
v___x_2752_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2752_, 0, v_numFields_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2741_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*2, v___x_2751_);
v_a_2744_ = v___x_2752_;
goto v___jp_2743_;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec(v_a_2740_);
v___x_2753_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc(v___y_2729_);
v___x_2754_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2753_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2754_);
v_a_2744_ = v_a_2755_;
goto v___jp_2743_;
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v_bs_x27_2742_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
v_a_2756_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2754_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
v___jp_2743_:
{
size_t v___x_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
v___x_2745_ = ((size_t)1ULL);
v___x_2746_ = lean_usize_add(v_i_2727_, v___x_2745_);
v___x_2747_ = lean_array_uset(v_bs_x27_2742_, v_i_2727_, v_a_2744_);
v_i_2727_ = v___x_2746_;
v_bs_2728_ = v___x_2747_;
goto _start;
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v_bs_2728_);
v_a_2764_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2739_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2739_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2772_, lean_object* v_i_2773_, lean_object* v_bs_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
size_t v_sz_boxed_2782_; size_t v_i_boxed_2783_; lean_object* v_res_2784_; 
v_sz_boxed_2782_ = lean_unbox_usize(v_sz_2772_);
lean_dec(v_sz_2772_);
v_i_boxed_2783_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_res_2784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2782_, v_i_boxed_2783_, v_bs_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
return v_res_2784_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_unsigned_to_nat(16u);
v___x_2787_ = lean_mk_array(v___x_2786_, v___x_2785_);
return v___x_2787_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2789_ = lean_unsigned_to_nat(0u);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v___x_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2793_, uint8_t v_alsoCasesOn_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = l_Lean_Expr_isApp(v_e_2793_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v_e_2793_);
v___x_2806_ = lean_box(0);
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
else
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_Expr_getAppFn(v_e_2793_);
if (lean_obj_tag(v___x_2808_) == 4)
{
lean_object* v_declName_2809_; lean_object* v_us_2810_; lean_object* v___x_2811_; lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2966_; 
v_declName_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_declName_2809_);
v_us_2810_ = lean_ctor_get(v___x_2808_, 1);
lean_inc(v_us_2810_);
lean_dec_ref(v___x_2808_);
lean_inc(v_declName_2809_);
v___x_2811_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2809_, v___y_2800_);
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2966_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2966_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_a_2812_) == 1)
{
lean_object* v_val_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
v_val_2816_ = lean_ctor_get(v_a_2812_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_a_2812_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2818_ = v_a_2812_;
v_isShared_2819_ = v_isSharedCheck_2858_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_val_2816_);
lean_dec(v_a_2812_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2858_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_dummy_2820_; lean_object* v_nargs_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v_args_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_dummy_2820_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
v_nargs_2821_ = l_Lean_Expr_getAppNumArgs(v_e_2793_);
lean_inc(v_nargs_2821_);
v___x_2822_ = lean_mk_array(v_nargs_2821_, v_dummy_2820_);
v___x_2823_ = lean_unsigned_to_nat(1u);
v___x_2824_ = lean_nat_sub(v_nargs_2821_, v___x_2823_);
lean_dec(v_nargs_2821_);
v_args_2825_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2793_, v___x_2822_, v___x_2824_);
v___x_2826_ = lean_array_get_size(v_args_2825_);
v___x_2827_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2816_);
v___x_2828_ = lean_nat_dec_lt(v___x_2826_, v___x_2827_);
lean_dec(v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v_numParams_2829_; lean_object* v_numDiscrs_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v_numParams_2829_ = lean_ctor_get(v_val_2816_, 0);
v_numDiscrs_2830_ = lean_ctor_get(v_val_2816_, 1);
v___x_2831_ = lean_array_mk(v_us_2810_);
v___x_2832_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2829_);
v___x_2833_ = l_Array_extract___redArg(v_args_2825_, v___x_2832_, v_numParams_2829_);
v___x_2834_ = l_Lean_instInhabitedExpr;
v___x_2835_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2816_);
v___x_2836_ = lean_array_get(v___x_2834_, v_args_2825_, v___x_2835_);
lean_dec(v___x_2835_);
v___x_2837_ = lean_nat_add(v_numParams_2829_, v___x_2823_);
v___x_2838_ = lean_nat_add(v___x_2837_, v_numDiscrs_2830_);
lean_inc(v___x_2838_);
lean_inc_ref(v_args_2825_);
v___x_2839_ = l_Array_toSubarray___redArg(v_args_2825_, v___x_2837_, v___x_2838_);
v___x_2840_ = l_Subarray_copy___redArg(v___x_2839_);
v___x_2841_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2816_);
v___x_2842_ = lean_nat_add(v___x_2838_, v___x_2841_);
lean_dec(v___x_2841_);
lean_inc(v___x_2842_);
lean_inc_ref(v_args_2825_);
v___x_2843_ = l_Array_toSubarray___redArg(v_args_2825_, v___x_2838_, v___x_2842_);
v___x_2844_ = l_Subarray_copy___redArg(v___x_2843_);
v___x_2845_ = l_Array_toSubarray___redArg(v_args_2825_, v___x_2842_, v___x_2826_);
v___x_2846_ = l_Subarray_copy___redArg(v___x_2845_);
v___x_2847_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2847_, 0, v_val_2816_);
lean_ctor_set(v___x_2847_, 1, v_declName_2809_);
lean_ctor_set(v___x_2847_, 2, v___x_2831_);
lean_ctor_set(v___x_2847_, 3, v___x_2833_);
lean_ctor_set(v___x_2847_, 4, v___x_2836_);
lean_ctor_set(v___x_2847_, 5, v___x_2840_);
lean_ctor_set(v___x_2847_, 6, v___x_2844_);
lean_ctor_set(v___x_2847_, 7, v___x_2846_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2847_);
v___x_2849_ = v___x_2818_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2851_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2849_);
v___x_2851_ = v___x_2814_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
lean_dec_ref(v_args_2825_);
lean_del_object(v___x_2818_);
lean_dec(v_val_2816_);
lean_dec(v_us_2810_);
lean_dec(v_declName_2809_);
v___x_2854_ = lean_box(0);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2854_);
v___x_2856_ = v___x_2814_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v___x_2859_; 
lean_del_object(v___x_2814_);
lean_dec(v_a_2812_);
v___x_2859_ = lean_st_ref_get(v___y_2800_);
if (v_alsoCasesOn_2794_ == 0)
{
lean_dec(v___x_2859_);
lean_dec(v_us_2810_);
lean_dec(v_declName_2809_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v_e_2793_);
goto v___jp_2802_;
}
else
{
lean_object* v_env_2860_; uint8_t v___x_2861_; 
v_env_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc_ref(v_env_2860_);
lean_dec(v___x_2859_);
lean_inc(v_declName_2809_);
v___x_2861_ = l_Lean_isCasesOnRecursor(v_env_2860_, v_declName_2809_);
if (v___x_2861_ == 0)
{
lean_dec(v_us_2810_);
lean_dec(v_declName_2809_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v_e_2793_);
goto v___jp_2802_;
}
else
{
lean_object* v_indName_2862_; lean_object* v___x_2863_; 
v_indName_2862_ = l_Lean_Name_getPrefix(v_declName_2809_);
lean_inc_ref(v___y_2799_);
v___x_2863_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2862_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2957_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2957_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2957_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
if (lean_obj_tag(v_a_2864_) == 5)
{
lean_object* v_val_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2952_; 
v_val_2868_ = lean_ctor_get(v_a_2864_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_a_2864_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2870_ = v_a_2864_;
v_isShared_2871_ = v_isSharedCheck_2952_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_val_2868_);
lean_dec(v_a_2864_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2952_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_toConstantVal_2872_; lean_object* v_numParams_2873_; lean_object* v_numIndices_2874_; lean_object* v_ctors_2875_; lean_object* v_nargs_2876_; lean_object* v_dummy_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v_args_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_toConstantVal_2872_ = lean_ctor_get(v_val_2868_, 0);
lean_inc_ref(v_toConstantVal_2872_);
v_numParams_2873_ = lean_ctor_get(v_val_2868_, 1);
lean_inc(v_numParams_2873_);
v_numIndices_2874_ = lean_ctor_get(v_val_2868_, 2);
lean_inc(v_numIndices_2874_);
v_ctors_2875_ = lean_ctor_get(v_val_2868_, 4);
lean_inc(v_ctors_2875_);
v_nargs_2876_ = l_Lean_Expr_getAppNumArgs(v_e_2793_);
v_dummy_2877_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
lean_inc(v_nargs_2876_);
v___x_2878_ = lean_mk_array(v_nargs_2876_, v_dummy_2877_);
v___x_2879_ = lean_unsigned_to_nat(1u);
v___x_2880_ = lean_nat_sub(v_nargs_2876_, v___x_2879_);
lean_dec(v_nargs_2876_);
v_args_2881_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2793_, v___x_2878_, v___x_2880_);
v___x_2882_ = lean_nat_add(v_numParams_2873_, v___x_2879_);
v___x_2883_ = lean_nat_add(v___x_2882_, v_numIndices_2874_);
v___x_2884_ = lean_nat_add(v___x_2883_, v___x_2879_);
lean_dec(v___x_2883_);
v___x_2885_ = l_Lean_InductiveVal_numCtors(v_val_2868_);
lean_dec_ref(v_val_2868_);
v___x_2886_ = lean_nat_add(v___x_2884_, v___x_2885_);
lean_dec(v___x_2885_);
v___x_2887_ = lean_array_get_size(v_args_2881_);
v___x_2888_ = lean_nat_dec_le(v___x_2886_, v___x_2887_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
lean_dec(v___x_2886_);
lean_dec(v___x_2884_);
lean_dec(v___x_2882_);
lean_dec_ref(v_args_2881_);
lean_dec(v_ctors_2875_);
lean_dec(v_numIndices_2874_);
lean_dec(v_numParams_2873_);
lean_dec_ref(v_toConstantVal_2872_);
lean_del_object(v___x_2870_);
lean_dec(v_us_2810_);
lean_dec(v_declName_2809_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
v___x_2889_ = lean_box(0);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2889_);
v___x_2891_ = v___x_2866_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
else
{
lean_object* v___x_2893_; lean_object* v_params_2894_; lean_object* v___x_2895_; lean_object* v_motive_2896_; lean_object* v_discrs_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v_discrInfos_2900_; lean_object* v_alts_2901_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v_lower_2943_; lean_object* v_upper_2944_; uint8_t v___x_2951_; 
lean_del_object(v___x_2866_);
v___x_2893_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2873_);
lean_inc_ref(v_args_2881_);
v_params_2894_ = l_Array_toSubarray___redArg(v_args_2881_, v___x_2893_, v_numParams_2873_);
v___x_2895_ = l_Lean_instInhabitedExpr;
v_motive_2896_ = lean_array_get(v___x_2895_, v_args_2881_, v_numParams_2873_);
lean_dec(v_numParams_2873_);
lean_inc(v___x_2884_);
lean_inc_ref(v_args_2881_);
v_discrs_2897_ = l_Array_toSubarray___redArg(v_args_2881_, v___x_2882_, v___x_2884_);
v___x_2898_ = lean_nat_add(v_numIndices_2874_, v___x_2879_);
lean_dec(v_numIndices_2874_);
v___x_2899_ = lean_box(0);
v_discrInfos_2900_ = lean_mk_array(v___x_2898_, v___x_2899_);
lean_inc(v___x_2886_);
lean_inc_ref(v_args_2881_);
v_alts_2901_ = l_Array_toSubarray___redArg(v_args_2881_, v___x_2884_, v___x_2886_);
v___x_2951_ = lean_nat_dec_le(v___x_2886_, v___x_2893_);
if (v___x_2951_ == 0)
{
v_lower_2943_ = v___x_2886_;
v_upper_2944_ = v___x_2887_;
goto v___jp_2942_;
}
else
{
lean_dec(v___x_2886_);
v_lower_2943_ = v___x_2893_;
v_upper_2944_ = v___x_2887_;
goto v___jp_2942_;
}
v___jp_2902_:
{
lean_object* v___x_2905_; size_t v_sz_2906_; size_t v___x_2907_; lean_object* v___x_2908_; 
v___x_2905_ = lean_array_mk(v_ctors_2875_);
v_sz_2906_ = lean_array_size(v___x_2905_);
v___x_2907_ = ((size_t)0ULL);
v___x_2908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2906_, v___x_2907_, v___x_2905_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2933_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2911_ = v___x_2908_;
v_isShared_2912_ = v_isSharedCheck_2933_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2933_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_start_2913_; lean_object* v_stop_2914_; lean_object* v_start_2915_; lean_object* v_stop_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
v_start_2913_ = lean_ctor_get(v_params_2894_, 1);
lean_inc(v_start_2913_);
v_stop_2914_ = lean_ctor_get(v_params_2894_, 2);
lean_inc(v_stop_2914_);
v_start_2915_ = lean_ctor_get(v_discrs_2897_, 1);
lean_inc(v_start_2915_);
v_stop_2916_ = lean_ctor_get(v_discrs_2897_, 2);
lean_inc(v_stop_2916_);
v___x_2917_ = lean_nat_sub(v_stop_2914_, v_start_2913_);
lean_dec(v_start_2913_);
lean_dec(v_stop_2914_);
v___x_2918_ = lean_nat_sub(v_stop_2916_, v_start_2915_);
lean_dec(v_start_2915_);
lean_dec(v_stop_2916_);
v___x_2919_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2920_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2917_);
lean_ctor_set(v___x_2920_, 1, v___x_2918_);
lean_ctor_set(v___x_2920_, 2, v_a_2909_);
lean_ctor_set(v___x_2920_, 3, v___y_2904_);
lean_ctor_set(v___x_2920_, 4, v_discrInfos_2900_);
lean_ctor_set(v___x_2920_, 5, v___x_2919_);
v___x_2921_ = lean_array_mk(v_us_2810_);
v___x_2922_ = l_Subarray_copy___redArg(v_params_2894_);
v___x_2923_ = l_Subarray_copy___redArg(v_discrs_2897_);
v___x_2924_ = l_Subarray_copy___redArg(v_alts_2901_);
v___x_2925_ = l_Subarray_copy___redArg(v___y_2903_);
v___x_2926_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2920_);
lean_ctor_set(v___x_2926_, 1, v_declName_2809_);
lean_ctor_set(v___x_2926_, 2, v___x_2921_);
lean_ctor_set(v___x_2926_, 3, v___x_2922_);
lean_ctor_set(v___x_2926_, 4, v_motive_2896_);
lean_ctor_set(v___x_2926_, 5, v___x_2923_);
lean_ctor_set(v___x_2926_, 6, v___x_2924_);
lean_ctor_set(v___x_2926_, 7, v___x_2925_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 1);
lean_ctor_set(v___x_2870_, 0, v___x_2926_);
v___x_2928_ = v___x_2870_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2930_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_2928_);
v___x_2930_ = v___x_2911_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec_ref(v_alts_2901_);
lean_dec_ref(v_discrInfos_2900_);
lean_dec_ref(v_discrs_2897_);
lean_dec(v_motive_2896_);
lean_dec_ref(v_params_2894_);
lean_del_object(v___x_2870_);
lean_dec(v_us_2810_);
lean_dec(v_declName_2809_);
v_a_2934_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2908_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2908_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
v___jp_2942_:
{
lean_object* v_levelParams_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v_levelParams_2945_ = lean_ctor_get(v_toConstantVal_2872_, 1);
lean_inc(v_levelParams_2945_);
lean_dec_ref(v_toConstantVal_2872_);
v___x_2946_ = l_Array_toSubarray___redArg(v_args_2881_, v_lower_2943_, v_upper_2944_);
v___x_2947_ = l_List_lengthTR___redArg(v_levelParams_2945_);
lean_dec(v_levelParams_2945_);
v___x_2948_ = l_List_lengthTR___redArg(v_us_2810_);
v___x_2949_ = lean_nat_dec_eq(v___x_2947_, v___x_2948_);
lean_dec(v___x_2948_);
lean_dec(v___x_2947_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
v___x_2950_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2903_ = v___x_2946_;
v___y_2904_ = v___x_2950_;
goto v___jp_2902_;
}
else
{
v___y_2903_ = v___x_2946_;
v___y_2904_ = v___x_2899_;
goto v___jp_2902_;
}
}
}
}
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
lean_dec(v_a_2864_);
lean_dec(v_us_2810_);
lean_dec(v_declName_2809_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v_e_2793_);
v___x_2953_ = lean_box(0);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2953_);
v___x_2955_ = v___x_2866_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v_us_2810_);
lean_dec(v_declName_2809_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v_e_2793_);
v_a_2958_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2863_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2863_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
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
lean_dec_ref(v___x_2808_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v_e_2793_);
goto v___jp_2802_;
}
}
v___jp_2802_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2967_, lean_object* v_alsoCasesOn_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2976_; lean_object* v_res_2977_; 
v_alsoCasesOn_boxed_2976_ = lean_unbox(v_alsoCasesOn_2968_);
v_res_2977_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2967_, v_alsoCasesOn_boxed_2976_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
if (lean_obj_tag(v_a_2978_) == 0)
{
lean_object* v___x_2980_; 
v___x_2980_ = l_List_reverse___redArg(v_a_2979_);
return v___x_2980_;
}
else
{
lean_object* v_head_2981_; lean_object* v_tail_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2991_; 
v_head_2981_ = lean_ctor_get(v_a_2978_, 0);
v_tail_2982_ = lean_ctor_get(v_a_2978_, 1);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_a_2978_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2984_ = v_a_2978_;
v_isShared_2985_ = v_isSharedCheck_2991_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_tail_2982_);
lean_inc(v_head_2981_);
lean_dec(v_a_2978_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2991_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2986_ = l_Lean_MessageData_ofExpr(v_head_2981_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v_a_2979_);
lean_ctor_set(v___x_2984_, 0, v___x_2986_);
v___x_2988_ = v___x_2984_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_a_2979_);
v___x_2988_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
v_a_2978_ = v_tail_2982_;
v_a_2979_ = v___x_2988_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
lean_object* v_fnName_2994_; uint8_t v___x_2995_; 
v_fnName_2994_ = lean_ctor_get(v_x_2993_, 0);
v___x_2995_ = l_Lean_Expr_isConstOf(v_x_2992_, v_fnName_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2996_, lean_object* v_x_2997_){
_start:
{
uint8_t v_res_2998_; lean_object* v_r_2999_; 
v_res_2998_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2996_, v_x_2997_);
lean_dec_ref(v_x_2997_);
lean_dec_ref(v_x_2996_);
v_r_2999_ = lean_box(v_res_2998_);
return v_r_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_3000_, lean_object* v_type_3001_, lean_object* v_val_3002_, lean_object* v_k_3003_, uint8_t v_nondep_3004_, uint8_t v_kind_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___f_3013_; lean_object* v___x_3014_; 
v___f_3013_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3013_, 0, v_k_3003_);
lean_closure_set(v___f_3013_, 1, v___y_3006_);
lean_closure_set(v___f_3013_, 2, v___y_3007_);
v___x_3014_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3000_, v_type_3001_, v_val_3002_, v___f_3013_, v_nondep_3004_, v_kind_3005_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
if (lean_obj_tag(v___x_3014_) == 0)
{
return v___x_3014_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_3023_, lean_object* v_type_3024_, lean_object* v_val_3025_, lean_object* v_k_3026_, lean_object* v_nondep_3027_, lean_object* v_kind_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
uint8_t v_nondep_boxed_3036_; uint8_t v_kind_boxed_3037_; lean_object* v_res_3038_; 
v_nondep_boxed_3036_ = lean_unbox(v_nondep_3027_);
v_kind_boxed_3037_ = lean_unbox(v_kind_3028_);
v_res_3038_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3023_, v_type_3024_, v_val_3025_, v_k_3026_, v_nondep_boxed_3036_, v_kind_boxed_3037_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_3039_, uint8_t v_usedLetOnly_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
lean_inc(v___y_3047_);
lean_inc_ref(v___y_3046_);
lean_inc(v___y_3045_);
lean_inc_ref(v___y_3044_);
lean_inc_ref(v_x_3041_);
v___x_3049_ = lean_apply_8(v_k_3039_, v_x_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, lean_box(0));
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; uint8_t v___x_3055_; lean_object* v___x_3056_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref(v___x_3049_);
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3052_ = lean_mk_empty_array_with_capacity(v___x_3051_);
v___x_3053_ = lean_array_push(v___x_3052_, v_x_3041_);
v___x_3054_ = 0;
v___x_3055_ = 1;
v___x_3056_ = l_Lean_Meta_mkLetFVars(v___x_3053_, v_a_3050_, v_usedLetOnly_3040_, v___x_3054_, v___x_3055_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec_ref(v___x_3053_);
return v___x_3056_;
}
else
{
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec_ref(v_x_3041_);
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_3057_, lean_object* v_usedLetOnly_3058_, lean_object* v_x_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
uint8_t v_usedLetOnly_boxed_3067_; lean_object* v_res_3068_; 
v_usedLetOnly_boxed_3067_ = lean_unbox(v_usedLetOnly_3058_);
v_res_3068_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_3057_, v_usedLetOnly_boxed_3067_, v_x_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_3069_, lean_object* v_type_3070_, lean_object* v_val_3071_, lean_object* v_k_3072_, uint8_t v_nondep_3073_, uint8_t v_kind_3074_, uint8_t v_usedLetOnly_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_box(v_usedLetOnly_3075_);
v___f_3084_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3084_, 0, v_k_3072_);
lean_closure_set(v___f_3084_, 1, v___x_3083_);
v___x_3085_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3069_, v_type_3070_, v_val_3071_, v___f_3084_, v_nondep_3073_, v_kind_3074_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_3086_, lean_object* v_type_3087_, lean_object* v_val_3088_, lean_object* v_k_3089_, lean_object* v_nondep_3090_, lean_object* v_kind_3091_, lean_object* v_usedLetOnly_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
uint8_t v_nondep_boxed_3100_; uint8_t v_kind_boxed_3101_; uint8_t v_usedLetOnly_boxed_3102_; lean_object* v_res_3103_; 
v_nondep_boxed_3100_ = lean_unbox(v_nondep_3090_);
v_kind_boxed_3101_ = lean_unbox(v_kind_3091_);
v_usedLetOnly_boxed_3102_ = lean_unbox(v_usedLetOnly_3092_);
v_res_3103_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_3086_, v_type_3087_, v_val_3088_, v_k_3089_, v_nondep_boxed_3100_, v_kind_boxed_3101_, v_usedLetOnly_boxed_3102_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_3104_, lean_object* v_positions_3105_, lean_object* v_recFnNames_3106_, lean_object* v_containsRecFn_3107_, lean_object* v_below_3108_, size_t v_sz_3109_, size_t v_i_3110_, lean_object* v_bs_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
uint8_t v___x_3119_; 
v___x_3119_ = lean_usize_dec_lt(v_i_3110_, v_sz_3109_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; 
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v_below_3108_);
lean_dec_ref(v_containsRecFn_3107_);
lean_dec_ref(v_recFnNames_3106_);
lean_dec_ref(v_positions_3105_);
lean_dec_ref(v_recArgInfos_3104_);
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v_bs_3111_);
return v___x_3120_;
}
else
{
lean_object* v_v_3121_; lean_object* v___x_3122_; 
v_v_3121_ = lean_array_uget_borrowed(v_bs_3111_, v_i_3110_);
lean_inc(v___y_3117_);
lean_inc_ref(v___y_3116_);
lean_inc(v___y_3115_);
lean_inc_ref(v___y_3114_);
lean_inc(v___y_3113_);
lean_inc(v___y_3112_);
lean_inc(v_v_3121_);
lean_inc_ref(v_below_3108_);
lean_inc_ref(v_containsRecFn_3107_);
lean_inc_ref(v_recFnNames_3106_);
lean_inc_ref(v_positions_3105_);
lean_inc_ref(v_recArgInfos_3104_);
v___x_3122_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3104_, v_positions_3105_, v_recFnNames_3106_, v_containsRecFn_3107_, v_below_3108_, v_v_3121_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3124_; lean_object* v_bs_x27_3125_; size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref(v___x_3122_);
v___x_3124_ = lean_unsigned_to_nat(0u);
v_bs_x27_3125_ = lean_array_uset(v_bs_3111_, v_i_3110_, v___x_3124_);
v___x_3126_ = ((size_t)1ULL);
v___x_3127_ = lean_usize_add(v_i_3110_, v___x_3126_);
v___x_3128_ = lean_array_uset(v_bs_x27_3125_, v_i_3110_, v_a_3123_);
v_i_3110_ = v___x_3127_;
v_bs_3111_ = v___x_3128_;
goto _start;
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v_bs_3111_);
lean_dec_ref(v_below_3108_);
lean_dec_ref(v_containsRecFn_3107_);
lean_dec_ref(v_recFnNames_3106_);
lean_dec_ref(v_positions_3105_);
lean_dec_ref(v_recArgInfos_3104_);
v_a_3130_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3122_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3122_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3140_ = l_Lean_stringToMessageData(v___x_3139_);
return v___x_3140_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3143_ = l_Lean_stringToMessageData(v___x_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3144_, lean_object* v_positions_3145_, lean_object* v_recFnNames_3146_, lean_object* v_containsRecFn_3147_, lean_object* v_below_3148_, lean_object* v_e_3149_, lean_object* v_x_3150_, lean_object* v_x_3151_, lean_object* v_x_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
if (lean_obj_tag(v_x_3150_) == 5)
{
lean_object* v_fn_3160_; lean_object* v_arg_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_fn_3160_ = lean_ctor_get(v_x_3150_, 0);
lean_inc_ref(v_fn_3160_);
v_arg_3161_ = lean_ctor_get(v_x_3150_, 1);
lean_inc_ref(v_arg_3161_);
lean_dec_ref(v_x_3150_);
v___x_3162_ = lean_array_set(v_x_3151_, v_x_3152_, v_arg_3161_);
v___x_3163_ = lean_unsigned_to_nat(1u);
v___x_3164_ = lean_nat_sub(v_x_3152_, v___x_3163_);
lean_dec(v_x_3152_);
v_x_3150_ = v_fn_3160_;
v_x_3151_ = v___x_3162_;
v_x_3152_ = v___x_3164_;
goto _start;
}
else
{
lean_object* v___f_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_dec(v_x_3152_);
lean_inc_ref(v_x_3150_);
v___f_3166_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3166_, 0, v_x_3150_);
v___x_3167_ = lean_unsigned_to_nat(0u);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3166_, v_recArgInfos_3144_, v___x_3167_);
if (lean_obj_tag(v___x_3168_) == 1)
{
lean_object* v_val_3169_; lean_object* v___x_3170_; lean_object* v___y_3172_; lean_object* v_recArgPos_3198_; lean_object* v_indGroupInst_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; 
lean_dec_ref(v_x_3150_);
v_val_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_val_3169_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = lean_array_fget_borrowed(v_recArgInfos_3144_, v_val_3169_);
v_recArgPos_3198_ = lean_ctor_get(v___x_3170_, 2);
v_indGroupInst_3199_ = lean_ctor_get(v___x_3170_, 4);
v___x_3200_ = lean_array_get_size(v_x_3151_);
v___x_3201_ = lean_nat_dec_lt(v_recArgPos_3198_, v___x_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
lean_dec(v_val_3169_);
lean_dec(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v_x_3151_);
lean_dec_ref(v_below_3148_);
lean_dec_ref(v_containsRecFn_3147_);
lean_dec_ref(v_recFnNames_3146_);
lean_dec_ref(v_positions_3145_);
lean_dec_ref(v_recArgInfos_3144_);
v___x_3202_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3203_ = l_Lean_indentExpr(v_e_3149_);
v___x_3204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3202_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3204_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_array_fget_borrowed(v_x_3151_, v_recArgPos_3198_);
lean_inc(v___y_3158_);
lean_inc_ref(v___y_3157_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc(v___x_3206_);
lean_inc_ref(v_below_3148_);
lean_inc_ref(v_containsRecFn_3147_);
lean_inc_ref(v_recFnNames_3146_);
lean_inc_ref(v_positions_3145_);
lean_inc_ref(v_recArgInfos_3144_);
v___x_3207_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3144_, v_positions_3145_, v_recFnNames_3146_, v_containsRecFn_3147_, v_below_3148_, v___x_3206_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v_params_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v___x_3207_);
v_params_3209_ = lean_ctor_get(v_indGroupInst_3199_, 2);
v___x_3210_ = lean_array_get_size(v_params_3209_);
lean_inc(v___y_3158_);
lean_inc_ref(v___y_3157_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc_ref(v_positions_3145_);
lean_inc_ref(v_below_3148_);
v___x_3211_ = l_Lean_Elab_Structural_toBelow(v_below_3148_, v___x_3210_, v_positions_3145_, v_val_3169_, v_a_3208_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_dec_ref(v_e_3149_);
v___y_3172_ = v___x_3211_;
goto v___jp_3171_;
}
else
{
lean_object* v_a_3212_; uint8_t v___y_3214_; uint8_t v___x_3219_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
v___x_3219_ = l_Lean_Exception_isInterrupt(v_a_3212_);
if (v___x_3219_ == 0)
{
uint8_t v___x_3220_; 
v___x_3220_ = l_Lean_Exception_isRuntime(v_a_3212_);
v___y_3214_ = v___x_3220_;
goto v___jp_3213_;
}
else
{
lean_dec(v_a_3212_);
v___y_3214_ = v___x_3219_;
goto v___jp_3213_;
}
v___jp_3213_:
{
if (v___y_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
lean_dec_ref(v___x_3211_);
v___x_3215_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3216_ = l_Lean_indentExpr(v_e_3149_);
v___x_3217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3215_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3217_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
v___y_3172_ = v___x_3218_;
goto v___jp_3171_;
}
else
{
lean_dec_ref(v_e_3149_);
v___y_3172_ = v___x_3211_;
goto v___jp_3171_;
}
}
}
}
else
{
lean_dec(v_val_3169_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v_x_3151_);
lean_dec_ref(v_e_3149_);
lean_dec_ref(v_below_3148_);
lean_dec_ref(v_containsRecFn_3147_);
lean_dec_ref(v_recFnNames_3146_);
lean_dec_ref(v_positions_3145_);
lean_dec_ref(v_recArgInfos_3144_);
return v___x_3207_;
}
}
v___jp_3171_:
{
if (lean_obj_tag(v___y_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v_fixedParamPerm_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v_snd_3177_; size_t v_sz_3178_; size_t v___x_3179_; lean_object* v___x_3180_; 
v_a_3173_ = lean_ctor_get(v___y_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref(v___y_3172_);
v_fixedParamPerm_3174_ = lean_ctor_get(v___x_3170_, 1);
v___x_3175_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3174_, v_x_3151_);
lean_dec_ref(v_x_3151_);
lean_inc(v___x_3170_);
v___x_3176_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3170_, v___x_3175_);
v_snd_3177_ = lean_ctor_get(v___x_3176_, 1);
lean_inc(v_snd_3177_);
lean_dec_ref(v___x_3176_);
v_sz_3178_ = lean_array_size(v_snd_3177_);
v___x_3179_ = ((size_t)0ULL);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3144_, v_positions_3145_, v_recFnNames_3146_, v_containsRecFn_3147_, v_below_3148_, v_sz_3178_, v___x_3179_, v_snd_3177_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3189_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3189_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3189_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3185_ = l_Lean_mkAppN(v_a_3173_, v_a_3181_);
lean_dec(v_a_3181_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3185_);
v___x_3187_ = v___x_3183_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_a_3173_);
v_a_3190_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3180_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3180_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v_x_3151_);
lean_dec_ref(v_below_3148_);
lean_dec_ref(v_containsRecFn_3147_);
lean_dec_ref(v_recFnNames_3146_);
lean_dec_ref(v_positions_3145_);
lean_dec_ref(v_recArgInfos_3144_);
return v___y_3172_;
}
}
}
else
{
lean_object* v___x_3221_; 
lean_dec(v___x_3168_);
lean_dec_ref(v_e_3149_);
lean_inc(v___y_3158_);
lean_inc_ref(v___y_3157_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc_ref(v_below_3148_);
lean_inc_ref(v_containsRecFn_3147_);
lean_inc_ref(v_recFnNames_3146_);
lean_inc_ref(v_positions_3145_);
lean_inc_ref(v_recArgInfos_3144_);
v___x_3221_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3144_, v_positions_3145_, v_recFnNames_3146_, v_containsRecFn_3147_, v_below_3148_, v_x_3150_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; size_t v_sz_3223_; size_t v___x_3224_; lean_object* v___x_3225_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref(v___x_3221_);
v_sz_3223_ = lean_array_size(v_x_3151_);
v___x_3224_ = ((size_t)0ULL);
v___x_3225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3144_, v_positions_3145_, v_recFnNames_3146_, v_containsRecFn_3147_, v_below_3148_, v_sz_3223_, v___x_3224_, v_x_3151_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3234_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = l_Lean_mkAppN(v_a_3222_, v_a_3226_);
lean_dec(v_a_3226_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3230_);
v___x_3232_ = v___x_3228_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec(v_a_3222_);
v_a_3235_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3225_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3225_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v_x_3151_);
lean_dec_ref(v_below_3148_);
lean_dec_ref(v_containsRecFn_3147_);
lean_dec_ref(v_recFnNames_3146_);
lean_dec_ref(v_positions_3145_);
lean_dec_ref(v_recArgInfos_3144_);
return v___x_3221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3243_, lean_object* v_recArgInfos_3244_, lean_object* v_positions_3245_, lean_object* v_recFnNames_3246_, lean_object* v_containsRecFn_3247_, lean_object* v_below_3248_, uint8_t v___x_3249_, uint8_t v_a_3250_, lean_object* v_x_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = lean_expr_instantiate1(v_body_3243_, v_x_3251_);
lean_inc(v___y_3257_);
lean_inc_ref(v___y_3256_);
lean_inc(v___y_3255_);
lean_inc_ref(v___y_3254_);
v___x_3260_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3244_, v_positions_3245_, v_recFnNames_3246_, v_containsRecFn_3247_, v_below_3248_, v___x_3259_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; lean_object* v___x_3266_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = lean_unsigned_to_nat(1u);
v___x_3263_ = lean_mk_empty_array_with_capacity(v___x_3262_);
v___x_3264_ = lean_array_push(v___x_3263_, v_x_3251_);
v___x_3265_ = 1;
v___x_3266_ = l_Lean_Meta_mkLambdaFVars(v___x_3264_, v_a_3261_, v___x_3249_, v_a_3250_, v___x_3249_, v_a_3250_, v___x_3265_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec_ref(v___x_3264_);
return v___x_3266_;
}
else
{
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec_ref(v_x_3251_);
return v___x_3260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3267_, lean_object* v_recArgInfos_3268_, lean_object* v_positions_3269_, lean_object* v_recFnNames_3270_, lean_object* v_containsRecFn_3271_, lean_object* v_below_3272_, lean_object* v___x_3273_, lean_object* v_a_3274_, lean_object* v_x_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
uint8_t v___x_49066__boxed_3283_; uint8_t v_a_49067__boxed_3284_; lean_object* v_res_3285_; 
v___x_49066__boxed_3283_ = lean_unbox(v___x_3273_);
v_a_49067__boxed_3284_ = lean_unbox(v_a_3274_);
v_res_3285_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3267_, v_recArgInfos_3268_, v_positions_3269_, v_recFnNames_3270_, v_containsRecFn_3271_, v_below_3272_, v___x_49066__boxed_3283_, v_a_49067__boxed_3284_, v_x_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec_ref(v_body_3267_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3286_, lean_object* v_recArgInfos_3287_, lean_object* v_positions_3288_, lean_object* v_recFnNames_3289_, lean_object* v_containsRecFn_3290_, lean_object* v_below_3291_, uint8_t v___x_3292_, uint8_t v_a_3293_, lean_object* v_x_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = lean_expr_instantiate1(v_body_3286_, v_x_3294_);
lean_inc(v___y_3300_);
lean_inc_ref(v___y_3299_);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3297_);
v___x_3303_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3287_, v_positions_3288_, v_recFnNames_3289_, v_containsRecFn_3290_, v_below_3291_, v___x_3302_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = lean_unsigned_to_nat(1u);
v___x_3306_ = lean_mk_empty_array_with_capacity(v___x_3305_);
v___x_3307_ = lean_array_push(v___x_3306_, v_x_3294_);
v___x_3308_ = 1;
v___x_3309_ = l_Lean_Meta_mkForallFVars(v___x_3307_, v_a_3304_, v___x_3292_, v_a_3293_, v_a_3293_, v___x_3308_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v___x_3307_);
return v___x_3309_;
}
else
{
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v_x_3294_);
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3310_, lean_object* v_recArgInfos_3311_, lean_object* v_positions_3312_, lean_object* v_recFnNames_3313_, lean_object* v_containsRecFn_3314_, lean_object* v_below_3315_, lean_object* v___x_3316_, lean_object* v_a_3317_, lean_object* v_x_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
uint8_t v___x_49085__boxed_3326_; uint8_t v_a_49086__boxed_3327_; lean_object* v_res_3328_; 
v___x_49085__boxed_3326_ = lean_unbox(v___x_3316_);
v_a_49086__boxed_3327_ = lean_unbox(v_a_3317_);
v_res_3328_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3310_, v_recArgInfos_3311_, v_positions_3312_, v_recFnNames_3313_, v_containsRecFn_3314_, v_below_3315_, v___x_49085__boxed_3326_, v_a_49086__boxed_3327_, v_x_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec_ref(v_body_3310_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3329_, lean_object* v_recArgInfos_3330_, lean_object* v_positions_3331_, lean_object* v_recFnNames_3332_, lean_object* v_containsRecFn_3333_, lean_object* v_below_3334_, lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3329_, v_recArgInfos_3330_, v_positions_3331_, v_recFnNames_3332_, v_containsRecFn_3333_, v_below_3334_, v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec_ref(v_x_3335_);
lean_dec_ref(v_body_3329_);
return v_res_3343_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__0));
v___x_3348_ = l_Lean_stringToMessageData(v___x_3347_);
return v___x_3348_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__2));
v___x_3351_ = l_Lean_stringToMessageData(v___x_3350_);
return v___x_3351_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__4));
v___x_3354_ = l_Lean_stringToMessageData(v___x_3353_);
return v___x_3354_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__6));
v___x_3357_ = l_Lean_stringToMessageData(v___x_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0(lean_object* v___x_3358_, lean_object* v_b_3359_, lean_object* v_recArgInfos_3360_, lean_object* v_positions_3361_, lean_object* v_recFnNames_3362_, lean_object* v_containsRecFn_3363_, uint8_t v___x_3364_, uint8_t v_a_3365_, lean_object* v___x_3366_, lean_object* v_a_3367_, lean_object* v_e_3368_, lean_object* v_xs_3369_, lean_object* v_altBody_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___x_3416_; lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3445_; 
lean_inc(v___x_3358_);
v___x_3416_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v___x_3358_, v___y_3375_);
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3445_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3445_;
goto v_resetjp_3418_;
}
v___jp_3378_:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = l_Lean_instInhabitedExpr;
v___x_3386_ = lean_array_get_borrowed(v___x_3385_, v_xs_3369_, v_b_3359_);
lean_dec(v_b_3359_);
lean_inc(v___y_3384_);
lean_inc_ref(v___y_3383_);
lean_inc(v___y_3382_);
lean_inc_ref(v___y_3381_);
lean_inc(v___x_3386_);
v___x_3387_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3360_, v_positions_3361_, v_recFnNames_3362_, v_containsRecFn_3363_, v___x_3386_, v_altBody_3370_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref(v___x_3387_);
v___x_3389_ = 1;
v___x_3390_ = l_Lean_Meta_mkLambdaFVars(v_xs_3369_, v_a_3388_, v___x_3364_, v_a_3365_, v___x_3364_, v_a_3365_, v___x_3389_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec_ref(v_xs_3369_);
return v___x_3390_;
}
else
{
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec_ref(v_xs_3369_);
return v___x_3387_;
}
}
v___jp_3391_:
{
lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3398_ = lean_array_get_size(v_xs_3369_);
v___x_3399_ = lean_nat_dec_eq(v___x_3398_, v___x_3366_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v_altBody_3370_);
lean_dec_ref(v_xs_3369_);
lean_dec_ref(v_containsRecFn_3363_);
lean_dec_ref(v_recFnNames_3362_);
lean_dec_ref(v_positions_3361_);
lean_dec_ref(v_recArgInfos_3360_);
lean_dec(v_b_3359_);
v___x_3400_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1);
v___x_3401_ = l_Lean_indentExpr(v_a_3367_);
v___x_3402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3400_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3);
v___x_3404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3402_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
v___x_3405_ = l_Lean_indentExpr(v_e_3368_);
v___x_3406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3406_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
else
{
lean_dec_ref(v_e_3368_);
lean_dec_ref(v_a_3367_);
v___y_3379_ = v___y_3392_;
v___y_3380_ = v___y_3393_;
v___y_3381_ = v___y_3394_;
v___y_3382_ = v___y_3395_;
v___y_3383_ = v___y_3396_;
v___y_3384_ = v___y_3397_;
goto v___jp_3378_;
}
}
v_resetjp_3418_:
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_unbox(v_a_3417_);
lean_dec(v_a_3417_);
if (v___x_3421_ == 0)
{
lean_del_object(v___x_3419_);
lean_dec(v___x_3358_);
v___y_3392_ = v___y_3371_;
v___y_3393_ = v___y_3372_;
v___y_3394_ = v___y_3373_;
v___y_3395_ = v___y_3374_;
v___y_3396_ = v___y_3375_;
v___y_3397_ = v___y_3376_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3422_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5);
lean_inc(v_b_3359_);
v___x_3423_ = l_Nat_reprFast(v_b_3359_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 3);
lean_ctor_set(v___x_3419_, 0, v___x_3423_);
v___x_3425_ = v___x_3419_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3426_ = l_Lean_MessageData_ofFormat(v___x_3425_);
v___x_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3422_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
lean_inc_ref(v_xs_3369_);
v___x_3430_ = lean_array_to_list(v_xs_3369_);
v___x_3431_ = lean_box(0);
v___x_3432_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v___x_3430_, v___x_3431_);
v___x_3433_ = l_Lean_MessageData_ofList(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3429_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v___x_3358_, v___x_3434_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_dec_ref(v___x_3435_);
v___y_3392_ = v___y_3371_;
v___y_3393_ = v___y_3372_;
v___y_3394_ = v___y_3373_;
v___y_3395_ = v___y_3374_;
v___y_3396_ = v___y_3375_;
v___y_3397_ = v___y_3376_;
goto v___jp_3391_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v_altBody_3370_);
lean_dec_ref(v_xs_3369_);
lean_dec_ref(v_e_3368_);
lean_dec_ref(v_a_3367_);
lean_dec_ref(v_containsRecFn_3363_);
lean_dec_ref(v_recFnNames_3362_);
lean_dec_ref(v_positions_3361_);
lean_dec_ref(v_recArgInfos_3360_);
lean_dec(v_b_3359_);
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___boxed(lean_object** _args){
lean_object* v___x_3446_ = _args[0];
lean_object* v_b_3447_ = _args[1];
lean_object* v_recArgInfos_3448_ = _args[2];
lean_object* v_positions_3449_ = _args[3];
lean_object* v_recFnNames_3450_ = _args[4];
lean_object* v_containsRecFn_3451_ = _args[5];
lean_object* v___x_3452_ = _args[6];
lean_object* v_a_3453_ = _args[7];
lean_object* v___x_3454_ = _args[8];
lean_object* v_a_3455_ = _args[9];
lean_object* v_e_3456_ = _args[10];
lean_object* v_xs_3457_ = _args[11];
lean_object* v_altBody_3458_ = _args[12];
lean_object* v___y_3459_ = _args[13];
lean_object* v___y_3460_ = _args[14];
lean_object* v___y_3461_ = _args[15];
lean_object* v___y_3462_ = _args[16];
lean_object* v___y_3463_ = _args[17];
lean_object* v___y_3464_ = _args[18];
lean_object* v___y_3465_ = _args[19];
_start:
{
uint8_t v___x_49163__boxed_3466_; uint8_t v_a_49164__boxed_3467_; lean_object* v_res_3468_; 
v___x_49163__boxed_3466_ = lean_unbox(v___x_3452_);
v_a_49164__boxed_3467_ = lean_unbox(v_a_3453_);
v_res_3468_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0(v___x_3446_, v_b_3447_, v_recArgInfos_3448_, v_positions_3449_, v_recFnNames_3450_, v_containsRecFn_3451_, v___x_49163__boxed_3466_, v_a_49164__boxed_3467_, v___x_3454_, v_a_3455_, v_e_3456_, v_xs_3457_, v_altBody_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
lean_dec(v___x_3454_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11(lean_object* v_recArgInfos_3469_, lean_object* v_positions_3470_, lean_object* v_recFnNames_3471_, lean_object* v_containsRecFn_3472_, uint8_t v_a_3473_, lean_object* v_e_3474_, lean_object* v_as_3475_, lean_object* v_bs_3476_, lean_object* v_i_3477_, lean_object* v_cs_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3486_ = lean_array_get_size(v_as_3475_);
v___x_3487_ = lean_nat_dec_lt(v_i_3477_, v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec(v_i_3477_);
lean_dec_ref(v_e_3474_);
lean_dec_ref(v_containsRecFn_3472_);
lean_dec_ref(v_recFnNames_3471_);
lean_dec_ref(v_positions_3470_);
lean_dec_ref(v_recArgInfos_3469_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_cs_3478_);
return v___x_3488_;
}
else
{
lean_object* v___x_3489_; uint8_t v___x_3490_; 
v___x_3489_ = lean_array_get_size(v_bs_3476_);
v___x_3490_ = lean_nat_dec_lt(v_i_3477_, v___x_3489_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; 
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec(v_i_3477_);
lean_dec_ref(v_e_3474_);
lean_dec_ref(v_containsRecFn_3472_);
lean_dec_ref(v_recFnNames_3471_);
lean_dec_ref(v_positions_3470_);
lean_dec_ref(v_recArgInfos_3469_);
v___x_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3491_, 0, v_cs_3478_);
return v___x_3491_;
}
else
{
uint8_t v___x_3492_; lean_object* v___x_3493_; lean_object* v_a_3494_; lean_object* v_b_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___f_3500_; lean_object* v___x_3501_; 
v___x_3492_ = 0;
v___x_3493_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3494_ = lean_array_fget_borrowed(v_as_3475_, v_i_3477_);
v_b_3495_ = lean_array_fget_borrowed(v_bs_3476_, v_i_3477_);
v___x_3496_ = lean_unsigned_to_nat(1u);
v___x_3497_ = lean_nat_add(v_b_3495_, v___x_3496_);
v___x_3498_ = lean_box(v___x_3492_);
v___x_3499_ = lean_box(v_a_3473_);
lean_inc_ref(v_e_3474_);
lean_inc(v_a_3494_);
lean_inc(v___x_3497_);
lean_inc_ref(v_containsRecFn_3472_);
lean_inc_ref(v_recFnNames_3471_);
lean_inc_ref(v_positions_3470_);
lean_inc_ref(v_recArgInfos_3469_);
lean_inc(v_b_3495_);
v___f_3500_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___boxed), 20, 11);
lean_closure_set(v___f_3500_, 0, v___x_3493_);
lean_closure_set(v___f_3500_, 1, v_b_3495_);
lean_closure_set(v___f_3500_, 2, v_recArgInfos_3469_);
lean_closure_set(v___f_3500_, 3, v_positions_3470_);
lean_closure_set(v___f_3500_, 4, v_recFnNames_3471_);
lean_closure_set(v___f_3500_, 5, v_containsRecFn_3472_);
lean_closure_set(v___f_3500_, 6, v___x_3498_);
lean_closure_set(v___f_3500_, 7, v___x_3499_);
lean_closure_set(v___f_3500_, 8, v___x_3497_);
lean_closure_set(v___f_3500_, 9, v_a_3494_);
lean_closure_set(v___f_3500_, 10, v_e_3474_);
lean_inc(v___y_3484_);
lean_inc_ref(v___y_3483_);
lean_inc(v___y_3482_);
lean_inc_ref(v___y_3481_);
lean_inc(v___y_3480_);
lean_inc(v___y_3479_);
lean_inc(v_a_3494_);
v___x_3501_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(v_a_3494_, v___x_3497_, v___f_3500_, v___x_3492_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = lean_nat_add(v_i_3477_, v___x_3496_);
lean_dec(v_i_3477_);
v___x_3504_ = lean_array_push(v_cs_3478_, v_a_3502_);
v_i_3477_ = v___x_3503_;
v_cs_3478_ = v___x_3504_;
goto _start;
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v_cs_3478_);
lean_dec(v_i_3477_);
lean_dec_ref(v_e_3474_);
lean_dec_ref(v_containsRecFn_3472_);
lean_dec_ref(v_recFnNames_3471_);
lean_dec_ref(v_positions_3470_);
lean_dec_ref(v_recArgInfos_3469_);
v_a_3506_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3501_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3501_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
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
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3516_ = l_Lean_stringToMessageData(v___x_3515_);
return v___x_3516_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3519_ = l_Lean_stringToMessageData(v___x_3518_);
return v___x_3519_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3523_, lean_object* v_positions_3524_, lean_object* v_recFnNames_3525_, lean_object* v_containsRecFn_3526_, lean_object* v_below_3527_, lean_object* v_e_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_e_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___x_3550_; 
lean_inc_ref(v_containsRecFn_3526_);
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc(v_a_3530_);
lean_inc(v_a_3529_);
lean_inc_ref(v_e_3528_);
v___x_3550_ = lean_apply_8(v_containsRecFn_3526_, v_e_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, lean_box(0));
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3778_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3778_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3778_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
uint8_t v___x_3555_; 
v___x_3555_ = lean_unbox(v_a_3551_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3557_; 
lean_dec(v_a_3551_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v_e_3528_);
v___x_3557_ = v___x_3553_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_e_3528_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
else
{
uint8_t v___x_3559_; 
lean_del_object(v___x_3553_);
v___x_3559_ = 0;
switch(lean_obj_tag(v_e_3528_))
{
case 6:
{
lean_object* v_binderName_3560_; lean_object* v_binderType_3561_; lean_object* v_body_3562_; uint8_t v_binderInfo_3563_; lean_object* v___x_3564_; 
v_binderName_3560_ = lean_ctor_get(v_e_3528_, 0);
lean_inc(v_binderName_3560_);
v_binderType_3561_ = lean_ctor_get(v_e_3528_, 1);
lean_inc_ref(v_binderType_3561_);
v_body_3562_ = lean_ctor_get(v_e_3528_, 2);
lean_inc_ref(v_body_3562_);
v_binderInfo_3563_ = lean_ctor_get_uint8(v_e_3528_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3528_);
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc(v_a_3530_);
lean_inc(v_a_3529_);
lean_inc_ref(v_below_3527_);
lean_inc_ref(v_containsRecFn_3526_);
lean_inc_ref(v_recFnNames_3525_);
lean_inc_ref(v_positions_3524_);
lean_inc_ref(v_recArgInfos_3523_);
v___x_3564_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3523_, v_positions_3524_, v_recFnNames_3525_, v_containsRecFn_3526_, v_below_3527_, v_binderType_3561_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3566_; lean_object* v___f_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref(v___x_3564_);
v___x_3566_ = lean_box(v___x_3559_);
v___f_3567_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 16, 8);
lean_closure_set(v___f_3567_, 0, v_body_3562_);
lean_closure_set(v___f_3567_, 1, v_recArgInfos_3523_);
lean_closure_set(v___f_3567_, 2, v_positions_3524_);
lean_closure_set(v___f_3567_, 3, v_recFnNames_3525_);
lean_closure_set(v___f_3567_, 4, v_containsRecFn_3526_);
lean_closure_set(v___f_3567_, 5, v_below_3527_);
lean_closure_set(v___f_3567_, 6, v___x_3566_);
lean_closure_set(v___f_3567_, 7, v_a_3551_);
v___x_3568_ = 0;
v___x_3569_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3560_, v_binderInfo_3563_, v_a_3565_, v___f_3567_, v___x_3568_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
return v___x_3569_;
}
else
{
lean_dec_ref(v_body_3562_);
lean_dec(v_binderName_3560_);
lean_dec(v_a_3551_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
return v___x_3564_;
}
}
case 7:
{
lean_object* v_binderName_3570_; lean_object* v_binderType_3571_; lean_object* v_body_3572_; uint8_t v_binderInfo_3573_; lean_object* v___x_3574_; 
v_binderName_3570_ = lean_ctor_get(v_e_3528_, 0);
lean_inc(v_binderName_3570_);
v_binderType_3571_ = lean_ctor_get(v_e_3528_, 1);
lean_inc_ref(v_binderType_3571_);
v_body_3572_ = lean_ctor_get(v_e_3528_, 2);
lean_inc_ref(v_body_3572_);
v_binderInfo_3573_ = lean_ctor_get_uint8(v_e_3528_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3528_);
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc(v_a_3530_);
lean_inc(v_a_3529_);
lean_inc_ref(v_below_3527_);
lean_inc_ref(v_containsRecFn_3526_);
lean_inc_ref(v_recFnNames_3525_);
lean_inc_ref(v_positions_3524_);
lean_inc_ref(v_recArgInfos_3523_);
v___x_3574_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3523_, v_positions_3524_, v_recFnNames_3525_, v_containsRecFn_3526_, v_below_3527_, v_binderType_3571_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3576_; lean_object* v___f_3577_; uint8_t v___x_3578_; lean_object* v___x_3579_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref(v___x_3574_);
v___x_3576_ = lean_box(v___x_3559_);
v___f_3577_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3577_, 0, v_body_3572_);
lean_closure_set(v___f_3577_, 1, v_recArgInfos_3523_);
lean_closure_set(v___f_3577_, 2, v_positions_3524_);
lean_closure_set(v___f_3577_, 3, v_recFnNames_3525_);
lean_closure_set(v___f_3577_, 4, v_containsRecFn_3526_);
lean_closure_set(v___f_3577_, 5, v_below_3527_);
lean_closure_set(v___f_3577_, 6, v___x_3576_);
lean_closure_set(v___f_3577_, 7, v_a_3551_);
v___x_3578_ = 0;
v___x_3579_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3570_, v_binderInfo_3573_, v_a_3575_, v___f_3577_, v___x_3578_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
return v___x_3579_;
}
else
{
lean_dec_ref(v_body_3572_);
lean_dec(v_binderName_3570_);
lean_dec(v_a_3551_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
return v___x_3574_;
}
}
case 8:
{
lean_object* v_declName_3580_; lean_object* v_type_3581_; lean_object* v_value_3582_; lean_object* v_body_3583_; uint8_t v_nondep_3584_; lean_object* v___x_3585_; 
lean_dec(v_a_3551_);
v_declName_3580_ = lean_ctor_get(v_e_3528_, 0);
lean_inc(v_declName_3580_);
v_type_3581_ = lean_ctor_get(v_e_3528_, 1);
lean_inc_ref(v_type_3581_);
v_value_3582_ = lean_ctor_get(v_e_3528_, 2);
lean_inc_ref(v_value_3582_);
v_body_3583_ = lean_ctor_get(v_e_3528_, 3);
lean_inc_ref(v_body_3583_);
v_nondep_3584_ = lean_ctor_get_uint8(v_e_3528_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3528_);
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc(v_a_3530_);
lean_inc(v_a_3529_);
lean_inc_ref(v_below_3527_);
lean_inc_ref(v_containsRecFn_3526_);
lean_inc_ref(v_recFnNames_3525_);
lean_inc_ref(v_positions_3524_);
lean_inc_ref(v_recArgInfos_3523_);
v___x_3585_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3523_, v_positions_3524_, v_recFnNames_3525_, v_containsRecFn_3526_, v_below_3527_, v_type_3581_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref(v___x_3585_);
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc(v_a_3530_);
lean_inc(v_a_3529_);
lean_inc_ref(v_below_3527_);
lean_inc_ref(v_containsRecFn_3526_);
lean_inc_ref(v_recFnNames_3525_);
lean_inc_ref(v_positions_3524_);
lean_inc_ref(v_recArgInfos_3523_);
v___x_3587_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3523_, v_positions_3524_, v_recFnNames_3525_, v_containsRecFn_3526_, v_below_3527_, v_value_3582_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___f_3589_; uint8_t v___x_3590_; lean_object* v___x_3591_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
lean_dec_ref(v___x_3587_);
v___f_3589_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 14, 6);
lean_closure_set(v___f_3589_, 0, v_body_3583_);
lean_closure_set(v___f_3589_, 1, v_recArgInfos_3523_);
lean_closure_set(v___f_3589_, 2, v_positions_3524_);
lean_closure_set(v___f_3589_, 3, v_recFnNames_3525_);
lean_closure_set(v___f_3589_, 4, v_containsRecFn_3526_);
lean_closure_set(v___f_3589_, 5, v_below_3527_);
v___x_3590_ = 0;
v___x_3591_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3580_, v_a_3586_, v_a_3588_, v___f_3589_, v_nondep_3584_, v___x_3590_, v___x_3559_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
return v___x_3591_;
}
else
{
lean_dec(v_a_3586_);
lean_dec_ref(v_body_3583_);
lean_dec(v_declName_3580_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
return v___x_3587_;
}
}
else
{
lean_dec_ref(v_body_3583_);
lean_dec_ref(v_value_3582_);
lean_dec(v_declName_3580_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
return v___x_3585_;
}
}
case 10:
{
lean_object* v_data_3592_; lean_object* v_expr_3593_; lean_object* v___x_3594_; 
lean_dec(v_a_3551_);
v_data_3592_ = lean_ctor_get(v_e_3528_, 0);
lean_inc(v_data_3592_);
v_expr_3593_ = lean_ctor_get(v_e_3528_, 1);
lean_inc_ref(v_expr_3593_);
v___x_3594_ = l_Lean_getRecAppSyntax_x3f(v_e_3528_);
lean_dec_ref(v_e_3528_);
if (lean_obj_tag(v___x_3594_) == 1)
{
lean_object* v_val_3595_; lean_object* v_fileName_3596_; lean_object* v_fileMap_3597_; lean_object* v_options_3598_; lean_object* v_currRecDepth_3599_; lean_object* v_maxRecDepth_3600_; lean_object* v_ref_3601_; lean_object* v_currNamespace_3602_; lean_object* v_openDecls_3603_; lean_object* v_initHeartbeats_3604_; lean_object* v_maxHeartbeats_3605_; lean_object* v_quotContext_3606_; lean_object* v_currMacroScope_3607_; uint8_t v_diag_3608_; lean_object* v_cancelTk_x3f_3609_; uint8_t v_suppressElabErrors_3610_; lean_object* v_inheritedTraceOptions_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v_data_3592_);
v_val_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_val_3595_);
lean_dec_ref(v___x_3594_);
v_fileName_3596_ = lean_ctor_get(v_a_3533_, 0);
v_fileMap_3597_ = lean_ctor_get(v_a_3533_, 1);
v_options_3598_ = lean_ctor_get(v_a_3533_, 2);
v_currRecDepth_3599_ = lean_ctor_get(v_a_3533_, 3);
v_maxRecDepth_3600_ = lean_ctor_get(v_a_3533_, 4);
v_ref_3601_ = lean_ctor_get(v_a_3533_, 5);
v_currNamespace_3602_ = lean_ctor_get(v_a_3533_, 6);
v_openDecls_3603_ = lean_ctor_get(v_a_3533_, 7);
v_initHeartbeats_3604_ = lean_ctor_get(v_a_3533_, 8);
v_maxHeartbeats_3605_ = lean_ctor_get(v_a_3533_, 9);
v_quotContext_3606_ = lean_ctor_get(v_a_3533_, 10);
v_currMacroScope_3607_ = lean_ctor_get(v_a_3533_, 11);
v_diag_3608_ = lean_ctor_get_uint8(v_a_3533_, sizeof(void*)*14);
v_cancelTk_x3f_3609_ = lean_ctor_get(v_a_3533_, 12);
v_suppressElabErrors_3610_ = lean_ctor_get_uint8(v_a_3533_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3611_ = lean_ctor_get(v_a_3533_, 13);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_a_3533_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3613_ = v_a_3533_;
v_isShared_3614_ = v_isSharedCheck_3620_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_inheritedTraceOptions_3611_);
lean_inc(v_cancelTk_x3f_3609_);
lean_inc(v_currMacroScope_3607_);
lean_inc(v_quotContext_3606_);
lean_inc(v_maxHeartbeats_3605_);
lean_inc(v_initHeartbeats_3604_);
lean_inc(v_openDecls_3603_);
lean_inc(v_currNamespace_3602_);
lean_inc(v_ref_3601_);
lean_inc(v_maxRecDepth_3600_);
lean_inc(v_currRecDepth_3599_);
lean_inc(v_options_3598_);
lean_inc(v_fileMap_3597_);
lean_inc(v_fileName_3596_);
lean_dec(v_a_3533_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3620_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v_ref_3615_; lean_object* v___x_3617_; 
v_ref_3615_ = l_Lean_replaceRef(v_val_3595_, v_ref_3601_);
lean_dec(v_ref_3601_);
lean_dec(v_val_3595_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 5, v_ref_3615_);
v___x_3617_ = v___x_3613_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_fileName_3596_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_fileMap_3597_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_options_3598_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_currRecDepth_3599_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_maxRecDepth_3600_);
lean_ctor_set(v_reuseFailAlloc_3619_, 5, v_ref_3615_);
lean_ctor_set(v_reuseFailAlloc_3619_, 6, v_currNamespace_3602_);
lean_ctor_set(v_reuseFailAlloc_3619_, 7, v_openDecls_3603_);
lean_ctor_set(v_reuseFailAlloc_3619_, 8, v_initHeartbeats_3604_);
lean_ctor_set(v_reuseFailAlloc_3619_, 9, v_maxHeartbeats_3605_);
lean_ctor_set(v_reuseFailAlloc_3619_, 10, v_quotContext_3606_);
lean_ctor_set(v_reuseFailAlloc_3619_, 11, v_currMacroScope_3607_);
lean_ctor_set(v_reuseFailAlloc_3619_, 12, v_cancelTk_x3f_3609_);
lean_ctor_set(v_reuseFailAlloc_3619_, 13, v_inheritedTraceOptions_3611_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, sizeof(void*)*14, v_diag_3608_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, sizeof(void*)*14 + 1, v_suppressElabErrors_3610_);
v___x_3617_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
v_e_3528_ = v_expr_3593_;
v_a_3533_ = v___x_3617_;
goto _start;
}
}
}
else
{
lean_object* v___x_3621_; 
lean_dec(v___x_3594_);
v___x_3621_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3523_, v_positions_3524_, v_recFnNames_3525_, v_containsRecFn_3526_, v_below_3527_, v_expr_3593_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3630_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3630_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3630_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3626_ = l_Lean_mkMData(v_data_3592_, v_a_3622_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3626_);
v___x_3628_ = v___x_3624_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
else
{
lean_dec(v_data_3592_);
return v___x_3621_;
}
}
}
case 11:
{
lean_object* v_typeName_3631_; lean_object* v_idx_3632_; lean_object* v_struct_3633_; lean_object* v___x_3634_; 
lean_dec(v_a_3551_);
v_typeName_3631_ = lean_ctor_get(v_e_3528_, 0);
lean_inc(v_typeName_3631_);
v_idx_3632_ = lean_ctor_get(v_e_3528_, 1);
lean_inc(v_idx_3632_);
v_struct_3633_ = lean_ctor_get(v_e_3528_, 2);
lean_inc_ref(v_struct_3633_);
lean_dec_ref(v_e_3528_);
v___x_3634_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3523_, v_positions_3524_, v_recFnNames_3525_, v_containsRecFn_3526_, v_below_3527_, v_struct_3633_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3643_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3643_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3643_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = l_Lean_mkProj(v_typeName_3631_, v_idx_3632_, v_a_3635_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 0, v___x_3639_);
v___x_3641_ = v___x_3637_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
else
{
lean_dec(v_idx_3632_);
lean_dec(v_typeName_3631_);
return v___x_3634_;
}
}
case 5:
{
uint8_t v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = lean_unbox(v_a_3551_);
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc(v_a_3530_);
lean_inc(v_a_3529_);
lean_inc_ref(v_e_3528_);
v___x_3645_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3528_, v___x_3644_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref(v___x_3645_);
if (lean_obj_tag(v_a_3646_) == 0)
{
lean_dec(v_a_3551_);
v_e_3537_ = v_e_3528_;
v___y_3538_ = v_a_3529_;
v___y_3539_ = v_a_3530_;
v___y_3540_ = v_a_3531_;
v___y_3541_ = v_a_3532_;
v___y_3542_ = v_a_3533_;
v___y_3543_ = v_a_3534_;
goto v___jp_3536_;
}
else
{
lean_object* v_val_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v_val_3647_ = lean_ctor_get(v_a_3646_, 0);
lean_inc(v_val_3647_);
lean_dec_ref(v_a_3646_);
v___x_3648_ = lean_unsigned_to_nat(0u);
v___x_3649_ = lean_array_get_size(v_recArgInfos_3523_);
v___x_3650_ = lean_nat_dec_lt(v___x_3648_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_dec(v_val_3647_);
lean_dec(v_a_3551_);
v_e_3537_ = v_e_3528_;
v___y_3538_ = v_a_3529_;
v___y_3539_ = v_a_3530_;
v___y_3540_ = v_a_3531_;
v___y_3541_ = v_a_3532_;
v___y_3542_ = v_a_3533_;
v___y_3543_ = v_a_3534_;
goto v___jp_3536_;
}
else
{
if (v___x_3650_ == 0)
{
lean_dec(v_val_3647_);
lean_dec(v_a_3551_);
v_e_3537_ = v_e_3528_;
v___y_3538_ = v_a_3529_;
v___y_3539_ = v_a_3530_;
v___y_3540_ = v_a_3531_;
v___y_3541_ = v_a_3532_;
v___y_3542_ = v_a_3533_;
v___y_3543_ = v_a_3534_;
goto v___jp_3536_;
}
else
{
size_t v___x_3651_; size_t v___x_3652_; uint8_t v___x_3653_; 
v___x_3651_ = ((size_t)0ULL);
v___x_3652_ = lean_usize_of_nat(v___x_3649_);
v___x_3653_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3528_, v_recArgInfos_3523_, v___x_3651_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_dec(v_val_3647_);
lean_dec(v_a_3551_);
v_e_3537_ = v_e_3528_;
v___y_3538_ = v_a_3529_;
v___y_3539_ = v_a_3530_;
v___y_3540_ = v_a_3531_;
v___y_3541_ = v_a_3532_;
v___y_3542_ = v_a_3533_;
v___y_3543_ = v_a_3534_;
goto v___jp_3536_;
}
else
{
lean_object* v___x_3654_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___x_3724_; 
v___x_3654_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3724_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v___x_3654_, v_a_3533_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; uint8_t v___x_3726_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
v___x_3726_ = lean_unbox(v_a_3725_);
lean_dec(v_a_3725_);
if (v___x_3726_ == 0)
{
v___y_3656_ = v_a_3529_;
v___y_3657_ = v_a_3530_;
v___y_3658_ = v_a_3531_;
v___y_3659_ = v_a_3532_;
v___y_3660_ = v_a_3533_;
v___y_3661_ = v_a_3534_;
goto v___jp_3655_;
}
else
{
lean_object* v___x_3727_; 
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc_ref(v_below_3527_);
v___x_3727_ = lean_infer_type(v_below_3527_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3527_);
v___x_3730_ = l_Lean_MessageData_ofExpr(v_below_3527_);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l_Lean_MessageData_ofExpr(v_a_3728_);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v___x_3654_, v___x_3735_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_dec_ref(v___x_3736_);
v___y_3656_ = v_a_3529_;
v___y_3657_ = v_a_3530_;
v___y_3658_ = v_a_3531_;
v___y_3659_ = v_a_3532_;
v___y_3660_ = v_a_3533_;
v___y_3661_ = v_a_3534_;
goto v___jp_3655_;
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_val_3647_);
lean_dec_ref(v_e_3528_);
lean_dec(v_a_3551_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_dec(v_val_3647_);
lean_dec_ref(v_e_3528_);
lean_dec(v_a_3551_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v_val_3647_);
lean_dec_ref(v_e_3528_);
lean_dec(v_a_3551_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
v_a_3745_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3724_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3724_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
v___jp_3655_:
{
lean_object* v___x_3662_; 
lean_inc(v___y_3661_);
lean_inc_ref(v___y_3660_);
lean_inc(v___y_3659_);
lean_inc_ref(v___y_3658_);
lean_inc_ref(v_below_3527_);
v___x_3662_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3647_, v_below_3527_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref(v___x_3662_);
if (lean_obj_tag(v_a_3663_) == 1)
{
lean_object* v_val_3664_; lean_object* v_toMatcherInfo_3665_; lean_object* v_matcherName_3666_; lean_object* v_matcherLevels_3667_; lean_object* v_params_3668_; lean_object* v_motive_3669_; lean_object* v_discrs_3670_; lean_object* v_alts_3671_; lean_object* v_remaining_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; lean_object* v___x_3676_; 
lean_dec_ref(v_below_3527_);
v_val_3664_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_val_3664_);
lean_dec_ref(v_a_3663_);
v_toMatcherInfo_3665_ = lean_ctor_get(v_val_3664_, 0);
lean_inc_ref(v_toMatcherInfo_3665_);
v_matcherName_3666_ = lean_ctor_get(v_val_3664_, 1);
lean_inc(v_matcherName_3666_);
v_matcherLevels_3667_ = lean_ctor_get(v_val_3664_, 2);
lean_inc_ref(v_matcherLevels_3667_);
v_params_3668_ = lean_ctor_get(v_val_3664_, 3);
lean_inc_ref(v_params_3668_);
v_motive_3669_ = lean_ctor_get(v_val_3664_, 4);
lean_inc_ref(v_motive_3669_);
v_discrs_3670_ = lean_ctor_get(v_val_3664_, 5);
lean_inc_ref(v_discrs_3670_);
v_alts_3671_ = lean_ctor_get(v_val_3664_, 6);
lean_inc_ref(v_alts_3671_);
v_remaining_3672_ = lean_ctor_get(v_val_3664_, 7);
lean_inc_ref(v_remaining_3672_);
v___x_3673_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3664_);
v___x_3674_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3675_ = lean_unbox(v_a_3551_);
lean_dec(v_a_3551_);
v___x_3676_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11(v_recArgInfos_3523_, v_positions_3524_, v_recFnNames_3525_, v_containsRecFn_3526_, v___x_3675_, v_e_3528_, v_alts_3671_, v___x_3673_, v___x_3648_, v___x_3674_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec_ref(v___x_3673_);
lean_dec_ref(v_alts_3671_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3686_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3686_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3686_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3681_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3681_, 0, v_toMatcherInfo_3665_);
lean_ctor_set(v___x_3681_, 1, v_matcherName_3666_);
lean_ctor_set(v___x_3681_, 2, v_matcherLevels_3667_);
lean_ctor_set(v___x_3681_, 3, v_params_3668_);
lean_ctor_set(v___x_3681_, 4, v_motive_3669_);
lean_ctor_set(v___x_3681_, 5, v_discrs_3670_);
lean_ctor_set(v___x_3681_, 6, v_a_3677_);
lean_ctor_set(v___x_3681_, 7, v_remaining_3672_);
v___x_3682_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3681_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3682_);
v___x_3684_ = v___x_3679_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec_ref(v_remaining_3672_);
lean_dec_ref(v_discrs_3670_);
lean_dec_ref(v_motive_3669_);
lean_dec_ref(v_params_3668_);
lean_dec_ref(v_matcherLevels_3667_);
lean_dec(v_matcherName_3666_);
lean_dec_ref(v_toMatcherInfo_3665_);
v_a_3687_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3676_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3676_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_object* v___x_3695_; 
lean_dec(v_a_3663_);
lean_dec(v_a_3551_);
v___x_3695_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v___x_3654_, v___y_3660_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; uint8_t v___x_3697_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref(v___x_3695_);
v___x_3697_ = lean_unbox(v_a_3696_);
lean_dec(v_a_3696_);
if (v___x_3697_ == 0)
{
v_e_3537_ = v_e_3528_;
v___y_3538_ = v___y_3656_;
v___y_3539_ = v___y_3657_;
v___y_3540_ = v___y_3658_;
v___y_3541_ = v___y_3659_;
v___y_3542_ = v___y_3660_;
v___y_3543_ = v___y_3661_;
goto v___jp_3536_;
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3699_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v___x_3654_, v___x_3698_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_dec_ref(v___x_3699_);
v_e_3537_ = v_e_3528_;
v___y_3538_ = v___y_3656_;
v___y_3539_ = v___y_3657_;
v___y_3540_ = v___y_3658_;
v___y_3541_ = v___y_3659_;
v___y_3542_ = v___y_3660_;
v___y_3543_ = v___y_3661_;
goto v___jp_3536_;
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v_e_3528_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v_e_3528_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
v_a_3708_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3695_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3695_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v_e_3528_);
lean_dec(v_a_3551_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
v_a_3716_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3662_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3662_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
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
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec_ref(v_e_3528_);
lean_dec(v_a_3551_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
v_a_3753_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3645_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3645_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
default: 
{
lean_object* v___x_3761_; 
lean_dec(v_a_3551_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
lean_inc_ref(v_e_3528_);
v___x_3761_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3525_, v_e_3528_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; 
v_unused_3769_ = lean_ctor_get(v___x_3761_, 0);
lean_dec(v_unused_3769_);
v___x_3763_ = v___x_3761_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_dec(v___x_3761_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v_e_3528_);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_e_3528_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v_e_3528_);
v_a_3770_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3761_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3761_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
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
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_e_3528_);
lean_dec_ref(v_below_3527_);
lean_dec_ref(v_containsRecFn_3526_);
lean_dec_ref(v_recFnNames_3525_);
lean_dec_ref(v_positions_3524_);
lean_dec_ref(v_recArgInfos_3523_);
v_a_3779_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3550_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3550_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
v___jp_3536_:
{
lean_object* v_dummy_3544_; lean_object* v_nargs_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v_dummy_3544_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
v_nargs_3545_ = l_Lean_Expr_getAppNumArgs(v_e_3537_);
lean_inc(v_nargs_3545_);
v___x_3546_ = lean_mk_array(v_nargs_3545_, v_dummy_3544_);
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_sub(v_nargs_3545_, v___x_3547_);
lean_dec(v_nargs_3545_);
lean_inc_ref(v_e_3537_);
v___x_3549_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3523_, v_positions_3524_, v_recFnNames_3525_, v_containsRecFn_3526_, v_below_3527_, v_e_3537_, v_e_3537_, v___x_3546_, v___x_3548_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
return v___x_3549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3787_, lean_object* v_recArgInfos_3788_, lean_object* v_positions_3789_, lean_object* v_recFnNames_3790_, lean_object* v_containsRecFn_3791_, lean_object* v_below_3792_, lean_object* v_x_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_expr_instantiate1(v_body_3787_, v_x_3793_);
v___x_3802_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3788_, v_positions_3789_, v_recFnNames_3790_, v_containsRecFn_3791_, v_below_3792_, v___x_3801_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3803_, lean_object* v_positions_3804_, lean_object* v_recFnNames_3805_, lean_object* v_containsRecFn_3806_, lean_object* v_below_3807_, lean_object* v_sz_3808_, lean_object* v_i_3809_, lean_object* v_bs_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
size_t v_sz_boxed_3818_; size_t v_i_boxed_3819_; lean_object* v_res_3820_; 
v_sz_boxed_3818_ = lean_unbox_usize(v_sz_3808_);
lean_dec(v_sz_3808_);
v_i_boxed_3819_ = lean_unbox_usize(v_i_3809_);
lean_dec(v_i_3809_);
v_res_3820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3803_, v_positions_3804_, v_recFnNames_3805_, v_containsRecFn_3806_, v_below_3807_, v_sz_boxed_3818_, v_i_boxed_3819_, v_bs_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___boxed(lean_object** _args){
lean_object* v_recArgInfos_3821_ = _args[0];
lean_object* v_positions_3822_ = _args[1];
lean_object* v_recFnNames_3823_ = _args[2];
lean_object* v_containsRecFn_3824_ = _args[3];
lean_object* v_a_3825_ = _args[4];
lean_object* v_e_3826_ = _args[5];
lean_object* v_as_3827_ = _args[6];
lean_object* v_bs_3828_ = _args[7];
lean_object* v_i_3829_ = _args[8];
lean_object* v_cs_3830_ = _args[9];
lean_object* v___y_3831_ = _args[10];
lean_object* v___y_3832_ = _args[11];
lean_object* v___y_3833_ = _args[12];
lean_object* v___y_3834_ = _args[13];
lean_object* v___y_3835_ = _args[14];
lean_object* v___y_3836_ = _args[15];
lean_object* v___y_3837_ = _args[16];
_start:
{
uint8_t v_a_49121__boxed_3838_; lean_object* v_res_3839_; 
v_a_49121__boxed_3838_ = lean_unbox(v_a_3825_);
v_res_3839_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11(v_recArgInfos_3821_, v_positions_3822_, v_recFnNames_3823_, v_containsRecFn_3824_, v_a_49121__boxed_3838_, v_e_3826_, v_as_3827_, v_bs_3828_, v_i_3829_, v_cs_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec_ref(v_bs_3828_);
lean_dec_ref(v_as_3827_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3840_, lean_object* v_positions_3841_, lean_object* v_recFnNames_3842_, lean_object* v_containsRecFn_3843_, lean_object* v_below_3844_, lean_object* v_e_3845_, lean_object* v_x_3846_, lean_object* v_x_3847_, lean_object* v_x_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3840_, v_positions_3841_, v_recFnNames_3842_, v_containsRecFn_3843_, v_below_3844_, v_e_3845_, v_x_3846_, v_x_3847_, v_x_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3857_, lean_object* v_positions_3858_, lean_object* v_recFnNames_3859_, lean_object* v_containsRecFn_3860_, lean_object* v_below_3861_, lean_object* v_e_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3857_, v_positions_3858_, v_recFnNames_3859_, v_containsRecFn_3860_, v_below_3861_, v_e_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3871_, lean_object* v_msg_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3872_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3881_, lean_object* v_msg_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3881_, v_msg_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec(v___y_3883_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3891_, lean_object* v_name_3892_, lean_object* v_type_3893_, lean_object* v_val_3894_, lean_object* v_k_3895_, uint8_t v_nondep_3896_, uint8_t v_kind_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3892_, v_type_3893_, v_val_3894_, v_k_3895_, v_nondep_3896_, v_kind_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3906_, lean_object* v_name_3907_, lean_object* v_type_3908_, lean_object* v_val_3909_, lean_object* v_k_3910_, lean_object* v_nondep_3911_, lean_object* v_kind_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
uint8_t v_nondep_boxed_3920_; uint8_t v_kind_boxed_3921_; lean_object* v_res_3922_; 
v_nondep_boxed_3920_ = lean_unbox(v_nondep_3911_);
v_kind_boxed_3921_ = lean_unbox(v_kind_3912_);
v_res_3922_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3906_, v_name_3907_, v_type_3908_, v_val_3909_, v_k_3910_, v_nondep_boxed_3920_, v_kind_boxed_3921_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3923_, v___y_3929_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec(v___y_3933_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_cls_3941_, lean_object* v_msg_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_cls_3941_, v_msg_3942_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_cls_3951_, lean_object* v_msg_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_cls_3951_, v_msg_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec(v___y_3953_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9(lean_object* v_00_u03b1_3961_, lean_object* v_constName_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(v_constName_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b1_3971_, lean_object* v_constName_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9(v_00_u03b1_3971_, v_constName_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec(v___y_3973_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16(lean_object* v_00_u03b1_3981_, lean_object* v_ref_3982_, lean_object* v_constName_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(v_ref_3982_, v_constName_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3992_, lean_object* v_ref_3993_, lean_object* v_constName_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16(v_00_u03b1_3992_, v_ref_3993_, v_constName_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
lean_dec(v___y_4000_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec(v_ref_3993_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18(lean_object* v_00_u03b1_4003_, lean_object* v_ref_4004_, lean_object* v_msg_4005_, lean_object* v_declHint_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(v_ref_4004_, v_msg_4005_, v_declHint_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___boxed(lean_object* v_00_u03b1_4015_, lean_object* v_ref_4016_, lean_object* v_msg_4017_, lean_object* v_declHint_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18(v_00_u03b1_4015_, v_ref_4016_, v_msg_4017_, v_declHint_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec(v_ref_4016_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_4027_, lean_object* v_declHint_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_4027_, v_declHint_4028_, v___y_4034_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_4037_, lean_object* v_declHint_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20(v_msg_4037_, v_declHint_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_4047_, lean_object* v_ref_4048_, lean_object* v_msg_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(v_ref_4048_, v_msg_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_4058_, lean_object* v_ref_4059_, lean_object* v_msg_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20(v_00_u03b1_4058_, v_ref_4059_, v_msg_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec(v_ref_4059_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_4069_, lean_object* v_e_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v_fst_4080_; lean_object* v_snd_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4078_ = lean_st_ref_take(v___y_4071_);
v___x_4079_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_4069_, v_e_4070_, v___x_4078_);
v_fst_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_fst_4080_);
v_snd_4081_ = lean_ctor_get(v___x_4079_, 1);
lean_inc(v_snd_4081_);
lean_dec_ref(v___x_4079_);
v___x_4082_ = lean_st_ref_set(v___y_4071_, v_snd_4081_);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_fst_4080_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_4084_, lean_object* v_e_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_4084_, v_e_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v_recFnNames_4084_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_4094_, size_t v_i_4095_, lean_object* v_bs_4096_){
_start:
{
uint8_t v___x_4097_; 
v___x_4097_ = lean_usize_dec_lt(v_i_4095_, v_sz_4094_);
if (v___x_4097_ == 0)
{
return v_bs_4096_;
}
else
{
lean_object* v_v_4098_; lean_object* v_fnName_4099_; lean_object* v___x_4100_; lean_object* v_bs_x27_4101_; size_t v___x_4102_; size_t v___x_4103_; lean_object* v___x_4104_; 
v_v_4098_ = lean_array_uget_borrowed(v_bs_4096_, v_i_4095_);
v_fnName_4099_ = lean_ctor_get(v_v_4098_, 0);
lean_inc(v_fnName_4099_);
v___x_4100_ = lean_unsigned_to_nat(0u);
v_bs_x27_4101_ = lean_array_uset(v_bs_4096_, v_i_4095_, v___x_4100_);
v___x_4102_ = ((size_t)1ULL);
v___x_4103_ = lean_usize_add(v_i_4095_, v___x_4102_);
v___x_4104_ = lean_array_uset(v_bs_x27_4101_, v_i_4095_, v_fnName_4099_);
v_i_4095_ = v___x_4103_;
v_bs_4096_ = v___x_4104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_4106_, lean_object* v_i_4107_, lean_object* v_bs_4108_){
_start:
{
size_t v_sz_boxed_4109_; size_t v_i_boxed_4110_; lean_object* v_res_4111_; 
v_sz_boxed_4109_ = lean_unbox_usize(v_sz_4106_);
lean_dec(v_sz_4106_);
v_i_boxed_4110_ = lean_unbox_usize(v_i_4107_);
lean_dec(v_i_4107_);
v_res_4111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_4109_, v_i_boxed_4110_, v_bs_4108_);
return v_res_4111_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = lean_box(0);
v___x_4113_ = lean_unsigned_to_nat(16u);
v___x_4114_ = lean_mk_array(v___x_4113_, v___x_4112_);
return v___x_4114_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_4116_ = lean_unsigned_to_nat(0u);
v___x_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
lean_ctor_set(v___x_4117_, 1, v___x_4115_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_4118_, lean_object* v_positions_4119_, lean_object* v_below_4120_, lean_object* v_e_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; size_t v_sz_4130_; size_t v___x_4131_; lean_object* v_recFnNames_4132_; lean_object* v_containsRecFn_4133_; lean_object* v___x_4134_; 
v___x_4128_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_4129_ = lean_st_mk_ref(v___x_4128_);
v_sz_4130_ = lean_array_size(v_recArgInfos_4118_);
v___x_4131_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_4118_);
v_recFnNames_4132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_4130_, v___x_4131_, v_recArgInfos_4118_);
lean_inc_ref(v_recFnNames_4132_);
v_containsRecFn_4133_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 9, 1);
lean_closure_set(v_containsRecFn_4133_, 0, v_recFnNames_4132_);
lean_inc(v___x_4129_);
v___x_4134_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_4118_, v_positions_4119_, v_recFnNames_4132_, v_containsRecFn_4133_, v_below_4120_, v_e_4121_, v___x_4129_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4143_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4143_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4143_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4139_; lean_object* v___x_4141_; 
v___x_4139_ = lean_st_ref_get(v___x_4129_);
lean_dec(v___x_4129_);
lean_dec(v___x_4139_);
if (v_isShared_4138_ == 0)
{
v___x_4141_ = v___x_4137_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4135_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
else
{
lean_dec(v___x_4129_);
return v___x_4134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_4144_, lean_object* v_positions_4145_, lean_object* v_below_4146_, lean_object* v_e_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4144_, v_positions_4145_, v_below_4146_, v_e_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___lam__0(lean_object* v_k_4155_, lean_object* v___y_4156_, lean_object* v_b_4157_, lean_object* v_c_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_apply_8(v_k_4155_, v_b_4157_, v_c_4158_, v___y_4156_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, lean_box(0));
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___lam__0___boxed(lean_object* v_k_4165_, lean_object* v___y_4166_, lean_object* v_b_4167_, lean_object* v_c_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___lam__0(v_k_4165_, v___y_4166_, v_b_4167_, v_c_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_4175_, lean_object* v_k_4176_, uint8_t v_cleanupAnnotations_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v___f_4184_; uint8_t v___x_4185_; uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___f_4184_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4184_, 0, v_k_4176_);
lean_closure_set(v___f_4184_, 1, v___y_4178_);
v___x_4185_ = 1;
v___x_4186_ = 0;
v___x_4187_ = lean_box(0);
v___x_4188_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4175_, v___x_4185_, v___x_4186_, v___x_4185_, v___x_4186_, v___x_4187_, v___f_4184_, v_cleanupAnnotations_4177_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
if (lean_obj_tag(v___x_4188_) == 0)
{
return v___x_4188_;
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4188_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4188_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4197_, lean_object* v_k_4198_, lean_object* v_cleanupAnnotations_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4206_; lean_object* v_res_4207_; 
v_cleanupAnnotations_boxed_4206_ = lean_unbox(v_cleanupAnnotations_4199_);
v_res_4207_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4197_, v_k_4198_, v_cleanupAnnotations_boxed_4206_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4208_, lean_object* v_e_4209_, lean_object* v_k_4210_, uint8_t v_cleanupAnnotations_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4209_, v_k_4210_, v_cleanupAnnotations_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4219_, lean_object* v_e_4220_, lean_object* v_k_4221_, lean_object* v_cleanupAnnotations_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4229_; lean_object* v_res_4230_; 
v_cleanupAnnotations_boxed_4229_ = lean_unbox(v_cleanupAnnotations_4222_);
v_res_4230_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4219_, v_e_4220_, v_k_4221_, v_cleanupAnnotations_boxed_4229_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_recArgInfo_4231_, lean_object* v_xs_4232_, lean_object* v_value_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v___x_4240_; 
lean_inc(v___y_4238_);
lean_inc_ref(v___y_4237_);
lean_inc(v___y_4236_);
lean_inc_ref(v___y_4235_);
v___x_4240_ = lean_infer_type(v_value_4233_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4242_; lean_object* v_fst_4243_; lean_object* v_snd_4244_; lean_object* v___x_4245_; uint8_t v___x_4246_; uint8_t v___x_4247_; uint8_t v___x_4248_; lean_object* v___x_4249_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref(v___x_4240_);
v___x_4242_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4231_, v_xs_4232_);
v_fst_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_fst_4243_);
v_snd_4244_ = lean_ctor_get(v___x_4242_, 1);
lean_inc(v_snd_4244_);
lean_dec_ref(v___x_4242_);
v___x_4245_ = l_Lean_Expr_headBeta(v_a_4241_);
v___x_4246_ = 0;
v___x_4247_ = 1;
v___x_4248_ = 1;
v___x_4249_ = l_Lean_Meta_mkForallFVars(v_snd_4244_, v___x_4245_, v___x_4246_, v___x_4247_, v___x_4247_, v___x_4248_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
lean_dec(v_snd_4244_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_a_4250_; lean_object* v___x_4251_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref(v___x_4249_);
v___x_4251_ = l_Lean_Meta_mkLambdaFVars(v_fst_4243_, v_a_4250_, v___x_4246_, v___x_4247_, v___x_4246_, v___x_4247_, v___x_4248_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v_fst_4243_);
return v___x_4251_;
}
else
{
lean_dec(v_fst_4243_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
return v___x_4249_;
}
}
else
{
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec_ref(v_xs_4232_);
lean_dec_ref(v_recArgInfo_4231_);
return v___x_4240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_recArgInfo_4252_, lean_object* v_xs_4253_, lean_object* v_value_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_recArgInfo_4252_, v_xs_4253_, v_value_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4255_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4262_, lean_object* v_value_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v___f_4270_; uint8_t v___x_4271_; lean_object* v___x_4272_; 
v___f_4270_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4270_, 0, v_recArgInfo_4262_);
v___x_4271_ = 0;
v___x_4272_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4263_, v___f_4270_, v___x_4271_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4273_, lean_object* v_value_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4273_, v_value_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4282_, lean_object* v_maxFVars_x3f_4283_, lean_object* v_k_4284_, uint8_t v_cleanupAnnotations_4285_, uint8_t v_whnfType_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v___f_4293_; lean_object* v___x_4294_; 
v___f_4293_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4293_, 0, v_k_4284_);
lean_closure_set(v___f_4293_, 1, v___y_4287_);
v___x_4294_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4282_, v_maxFVars_x3f_4283_, v___f_4293_, v_cleanupAnnotations_4285_, v_whnfType_4286_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4294_) == 0)
{
return v___x_4294_;
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4303_, lean_object* v_maxFVars_x3f_4304_, lean_object* v_k_4305_, lean_object* v_cleanupAnnotations_4306_, lean_object* v_whnfType_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4314_; uint8_t v_whnfType_boxed_4315_; lean_object* v_res_4316_; 
v_cleanupAnnotations_boxed_4314_ = lean_unbox(v_cleanupAnnotations_4306_);
v_whnfType_boxed_4315_ = lean_unbox(v_whnfType_4307_);
v_res_4316_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4303_, v_maxFVars_x3f_4304_, v_k_4305_, v_cleanupAnnotations_boxed_4314_, v_whnfType_boxed_4315_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4317_, lean_object* v_type_4318_, lean_object* v_maxFVars_x3f_4319_, lean_object* v_k_4320_, uint8_t v_cleanupAnnotations_4321_, uint8_t v_whnfType_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4318_, v_maxFVars_x3f_4319_, v_k_4320_, v_cleanupAnnotations_4321_, v_whnfType_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4330_, lean_object* v_type_4331_, lean_object* v_maxFVars_x3f_4332_, lean_object* v_k_4333_, lean_object* v_cleanupAnnotations_4334_, lean_object* v_whnfType_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4342_; uint8_t v_whnfType_boxed_4343_; lean_object* v_res_4344_; 
v_cleanupAnnotations_boxed_4342_ = lean_unbox(v_cleanupAnnotations_4334_);
v_whnfType_boxed_4343_ = lean_unbox(v_whnfType_4335_);
v_res_4344_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4330_, v_type_4331_, v_maxFVars_x3f_4332_, v_k_4333_, v_cleanupAnnotations_boxed_4342_, v_whnfType_boxed_4343_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4345_, lean_object* v_recArgInfos_4346_, lean_object* v_positions_4347_, lean_object* v_value_4348_, lean_object* v_fst_4349_, lean_object* v_snd_4350_, lean_object* v_below_4351_, lean_object* v_x_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4359_ = lean_unsigned_to_nat(0u);
v___x_4360_ = lean_array_get_borrowed(v___x_4345_, v_below_4351_, v___x_4359_);
lean_inc(v___y_4357_);
lean_inc_ref(v___y_4356_);
lean_inc(v___y_4355_);
lean_inc_ref(v___y_4354_);
lean_inc(v___x_4360_);
v___x_4361_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4346_, v_positions_4347_, v___x_4360_, v_value_4348_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; uint8_t v___x_4369_; uint8_t v___x_4370_; lean_object* v___x_4371_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref(v___x_4361_);
v___x_4363_ = lean_unsigned_to_nat(1u);
v___x_4364_ = lean_mk_empty_array_with_capacity(v___x_4363_);
lean_inc(v___x_4360_);
v___x_4365_ = lean_array_push(v___x_4364_, v___x_4360_);
v___x_4366_ = l_Array_append___redArg(v_fst_4349_, v___x_4365_);
lean_dec_ref(v___x_4365_);
v___x_4367_ = l_Array_append___redArg(v___x_4366_, v_snd_4350_);
v___x_4368_ = 0;
v___x_4369_ = 1;
v___x_4370_ = 1;
v___x_4371_ = l_Lean_Meta_mkLambdaFVars(v___x_4367_, v_a_4362_, v___x_4368_, v___x_4369_, v___x_4368_, v___x_4369_, v___x_4370_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec_ref(v___x_4367_);
return v___x_4371_;
}
else
{
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec_ref(v_fst_4349_);
return v___x_4361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4372_, lean_object* v_recArgInfos_4373_, lean_object* v_positions_4374_, lean_object* v_value_4375_, lean_object* v_fst_4376_, lean_object* v_snd_4377_, lean_object* v_below_4378_, lean_object* v_x_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4372_, v_recArgInfos_4373_, v_positions_4374_, v_value_4375_, v_fst_4376_, v_snd_4377_, v_below_4378_, v_x_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec_ref(v_x_4379_);
lean_dec_ref(v_below_4378_);
lean_dec_ref(v_snd_4377_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4389_, lean_object* v_FType_4390_, lean_object* v___x_4391_, lean_object* v_recArgInfos_4392_, lean_object* v_positions_4393_, lean_object* v_xs_4394_, lean_object* v_value_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v___x_4402_; lean_object* v_fst_4403_; lean_object* v_snd_4404_; lean_object* v___x_4405_; 
v___x_4402_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4389_, v_xs_4394_);
v_fst_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_fst_4403_);
v_snd_4404_ = lean_ctor_get(v___x_4402_, 1);
lean_inc(v_snd_4404_);
lean_dec_ref(v___x_4402_);
lean_inc(v___y_4400_);
lean_inc_ref(v___y_4399_);
lean_inc(v___y_4398_);
lean_inc_ref(v___y_4397_);
v___x_4405_ = l_Lean_Meta_instantiateForall(v_FType_4390_, v_fst_4403_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___f_4407_; lean_object* v___x_4408_; uint8_t v___x_4409_; lean_object* v___x_4410_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___f_4407_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 14, 6);
lean_closure_set(v___f_4407_, 0, v___x_4391_);
lean_closure_set(v___f_4407_, 1, v_recArgInfos_4392_);
lean_closure_set(v___f_4407_, 2, v_positions_4393_);
lean_closure_set(v___f_4407_, 3, v_value_4395_);
lean_closure_set(v___f_4407_, 4, v_fst_4403_);
lean_closure_set(v___f_4407_, 5, v_snd_4404_);
v___x_4408_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4409_ = 0;
v___x_4410_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4406_, v___x_4408_, v___f_4407_, v___x_4409_, v___x_4409_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
return v___x_4410_;
}
else
{
lean_dec(v_snd_4404_);
lean_dec(v_fst_4403_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v___y_4396_);
lean_dec_ref(v_value_4395_);
lean_dec_ref(v_positions_4393_);
lean_dec_ref(v_recArgInfos_4392_);
lean_dec_ref(v___x_4391_);
return v___x_4405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4411_, lean_object* v_FType_4412_, lean_object* v___x_4413_, lean_object* v_recArgInfos_4414_, lean_object* v_positions_4415_, lean_object* v_xs_4416_, lean_object* v_value_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4411_, v_FType_4412_, v___x_4413_, v_recArgInfos_4414_, v_positions_4415_, v_xs_4416_, v_value_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4425_, lean_object* v_positions_4426_, lean_object* v_recArgInfo_4427_, lean_object* v_value_4428_, lean_object* v_FType_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v___x_4436_; lean_object* v___f_4437_; uint8_t v___x_4438_; lean_object* v___x_4439_; 
v___x_4436_ = l_Lean_instInhabitedExpr;
v___f_4437_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 13, 5);
lean_closure_set(v___f_4437_, 0, v_recArgInfo_4427_);
lean_closure_set(v___f_4437_, 1, v_FType_4429_);
lean_closure_set(v___f_4437_, 2, v___x_4436_);
lean_closure_set(v___f_4437_, 3, v_recArgInfos_4425_);
lean_closure_set(v___f_4437_, 4, v_positions_4426_);
v___x_4438_ = 0;
v___x_4439_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4428_, v___f_4437_, v___x_4438_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4440_, lean_object* v_positions_4441_, lean_object* v_recArgInfo_4442_, lean_object* v_value_4443_, lean_object* v_FType_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4440_, v_positions_4441_, v_recArgInfo_4442_, v_value_4443_, v_FType_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___redArg(lean_object* v_e_4452_, lean_object* v_k_4453_, uint8_t v_cleanupAnnotations_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___f_4460_; uint8_t v___x_4461_; uint8_t v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___f_4460_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4460_, 0, v_k_4453_);
v___x_4461_ = 1;
v___x_4462_ = 0;
v___x_4463_ = lean_box(0);
v___x_4464_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4452_, v___x_4461_, v___x_4462_, v___x_4461_, v___x_4462_, v___x_4463_, v___f_4460_, v_cleanupAnnotations_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4464_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4464_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4464_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
v_a_4473_ = lean_ctor_get(v___x_4464_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4464_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4464_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4464_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___redArg___boxed(lean_object* v_e_4481_, lean_object* v_k_4482_, lean_object* v_cleanupAnnotations_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4489_; lean_object* v_res_4490_; 
v_cleanupAnnotations_boxed_4489_ = lean_unbox(v_cleanupAnnotations_4483_);
v_res_4490_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___redArg(v_e_4481_, v_k_4482_, v_cleanupAnnotations_boxed_4489_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1(lean_object* v_00_u03b1_4491_, lean_object* v_e_4492_, lean_object* v_k_4493_, uint8_t v_cleanupAnnotations_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___redArg(v_e_4492_, v_k_4493_, v_cleanupAnnotations_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___boxed(lean_object* v_00_u03b1_4501_, lean_object* v_e_4502_, lean_object* v_k_4503_, lean_object* v_cleanupAnnotations_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4510_; lean_object* v_res_4511_; 
v_cleanupAnnotations_boxed_4510_ = lean_unbox(v_cleanupAnnotations_4504_);
v_res_4511_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1(v_00_u03b1_4501_, v_e_4502_, v_k_4503_, v_cleanupAnnotations_boxed_4510_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4512_, lean_object* v_params_4513_, uint8_t v_isIndPred_4514_, lean_object* v_brecOnUniv_4515_, lean_object* v_levels_4516_, lean_object* v_idx_4517_){
_start:
{
lean_object* v_n_4518_; lean_object* v___y_4520_; 
v_n_4518_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4512_, v_idx_4517_);
if (v_isIndPred_4514_ == 0)
{
lean_object* v___x_4523_; 
v___x_4523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4523_, 0, v_brecOnUniv_4515_);
lean_ctor_set(v___x_4523_, 1, v_levels_4516_);
v___y_4520_ = v___x_4523_;
goto v___jp_4519_;
}
else
{
lean_dec(v_brecOnUniv_4515_);
v___y_4520_ = v_levels_4516_;
goto v___jp_4519_;
}
v___jp_4519_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = l_Lean_Expr_const___override(v_n_4518_, v___y_4520_);
v___x_4522_ = l_Lean_mkAppN(v___x_4521_, v_params_4513_);
return v___x_4522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4524_, lean_object* v_params_4525_, lean_object* v_isIndPred_4526_, lean_object* v_brecOnUniv_4527_, lean_object* v_levels_4528_, lean_object* v_idx_4529_){
_start:
{
uint8_t v_isIndPred_boxed_4530_; lean_object* v_res_4531_; 
v_isIndPred_boxed_4530_ = lean_unbox(v_isIndPred_4526_);
v_res_4531_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4524_, v_params_4525_, v_isIndPred_boxed_4530_, v_brecOnUniv_4527_, v_levels_4528_, v_idx_4529_);
lean_dec(v_idx_4529_);
lean_dec_ref(v_params_4525_);
lean_dec_ref(v_toIndGroupInfo_4524_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4532_, lean_object* v_a_4533_, lean_object* v_n_4534_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = lean_apply_1(v_brecOnCons_4532_, v_n_4534_);
v___x_4536_ = l_Lean_mkAppN(v___x_4535_, v_a_4533_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4537_, lean_object* v_a_4538_, lean_object* v_n_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4537_, v_a_4538_, v_n_4539_);
lean_dec_ref(v_a_4538_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4541_, lean_object* v_type_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Lean_Meta_getLevel(v_type_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4549_, lean_object* v_type_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4549_, v_type_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
lean_dec_ref(v_x_4549_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(lean_object* v_inst_4557_, lean_object* v_xs_4558_, size_t v_sz_4559_, size_t v_i_4560_, lean_object* v_bs_4561_){
_start:
{
uint8_t v___x_4562_; 
v___x_4562_ = lean_usize_dec_lt(v_i_4560_, v_sz_4559_);
if (v___x_4562_ == 0)
{
lean_dec(v_inst_4557_);
return v_bs_4561_;
}
else
{
lean_object* v_v_4563_; lean_object* v___x_4564_; lean_object* v_bs_x27_4565_; lean_object* v___x_4566_; size_t v___x_4567_; size_t v___x_4568_; lean_object* v___x_4569_; 
v_v_4563_ = lean_array_uget(v_bs_4561_, v_i_4560_);
v___x_4564_ = lean_unsigned_to_nat(0u);
v_bs_x27_4565_ = lean_array_uset(v_bs_4561_, v_i_4560_, v___x_4564_);
lean_inc(v_inst_4557_);
v___x_4566_ = lean_array_get_borrowed(v_inst_4557_, v_xs_4558_, v_v_4563_);
lean_dec(v_v_4563_);
v___x_4567_ = ((size_t)1ULL);
v___x_4568_ = lean_usize_add(v_i_4560_, v___x_4567_);
lean_inc(v___x_4566_);
v___x_4569_ = lean_array_uset(v_bs_x27_4565_, v_i_4560_, v___x_4566_);
v_i_4560_ = v___x_4568_;
v_bs_4561_ = v___x_4569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg___boxed(lean_object* v_inst_4571_, lean_object* v_xs_4572_, lean_object* v_sz_4573_, lean_object* v_i_4574_, lean_object* v_bs_4575_){
_start:
{
size_t v_sz_boxed_4576_; size_t v_i_boxed_4577_; lean_object* v_res_4578_; 
v_sz_boxed_4576_ = lean_unbox_usize(v_sz_4573_);
lean_dec(v_sz_4573_);
v_i_boxed_4577_ = lean_unbox_usize(v_i_4574_);
lean_dec(v_i_4574_);
v_res_4578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(v_inst_4571_, v_xs_4572_, v_sz_boxed_4576_, v_i_boxed_4577_, v_bs_4575_);
lean_dec_ref(v_xs_4572_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_inst_4579_, lean_object* v_xs_4580_, lean_object* v_f_4581_, lean_object* v_as_4582_, lean_object* v_bs_4583_, lean_object* v_i_4584_, lean_object* v_cs_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v___x_4591_; uint8_t v___x_4592_; 
v___x_4591_ = lean_array_get_size(v_as_4582_);
v___x_4592_ = lean_nat_dec_lt(v_i_4584_, v___x_4591_);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; 
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec(v_i_4584_);
lean_dec_ref(v_f_4581_);
lean_dec(v_inst_4579_);
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v_cs_4585_);
return v___x_4593_;
}
else
{
lean_object* v___x_4594_; uint8_t v___x_4595_; 
v___x_4594_ = lean_array_get_size(v_bs_4583_);
v___x_4595_ = lean_nat_dec_lt(v_i_4584_, v___x_4594_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; 
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec(v_i_4584_);
lean_dec_ref(v_f_4581_);
lean_dec(v_inst_4579_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v_cs_4585_);
return v___x_4596_;
}
else
{
lean_object* v_a_4597_; lean_object* v_b_4598_; size_t v_sz_4599_; size_t v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v_a_4597_ = lean_array_fget_borrowed(v_as_4582_, v_i_4584_);
v_b_4598_ = lean_array_fget_borrowed(v_bs_4583_, v_i_4584_);
v_sz_4599_ = lean_array_size(v_b_4598_);
v___x_4600_ = ((size_t)0ULL);
lean_inc(v_b_4598_);
lean_inc(v_inst_4579_);
v___x_4601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(v_inst_4579_, v_xs_4580_, v_sz_4599_, v___x_4600_, v_b_4598_);
lean_inc_ref(v_f_4581_);
lean_inc(v___y_4589_);
lean_inc_ref(v___y_4588_);
lean_inc(v___y_4587_);
lean_inc_ref(v___y_4586_);
lean_inc(v_a_4597_);
v___x_4602_ = lean_apply_7(v_f_4581_, v_a_4597_, v___x_4601_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, lean_box(0));
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4603_);
lean_dec_ref(v___x_4602_);
v___x_4604_ = lean_unsigned_to_nat(1u);
v___x_4605_ = lean_nat_add(v_i_4584_, v___x_4604_);
lean_dec(v_i_4584_);
v___x_4606_ = lean_array_push(v_cs_4585_, v_a_4603_);
v_i_4584_ = v___x_4605_;
v_cs_4585_ = v___x_4606_;
goto _start;
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec_ref(v_cs_4585_);
lean_dec(v_i_4584_);
lean_dec_ref(v_f_4581_);
lean_dec(v_inst_4579_);
v_a_4608_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4602_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4602_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_inst_4616_, lean_object* v_xs_4617_, lean_object* v_f_4618_, lean_object* v_as_4619_, lean_object* v_bs_4620_, lean_object* v_i_4621_, lean_object* v_cs_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_inst_4616_, v_xs_4617_, v_f_4618_, v_as_4619_, v_bs_4620_, v_i_4621_, v_cs_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
lean_dec_ref(v_bs_4620_);
lean_dec_ref(v_as_4619_);
lean_dec_ref(v_xs_4617_);
return v_res_4628_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Array_instInhabited(lean_box(0));
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v___x_4636_; lean_object* v_toApplicative_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4698_; 
v___x_4636_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4637_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4698_ == 0)
{
lean_object* v_unused_4699_; 
v_unused_4699_ = lean_ctor_get(v___x_4636_, 1);
lean_dec(v_unused_4699_);
v___x_4639_ = v___x_4636_;
v_isShared_4640_ = v_isSharedCheck_4698_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_toApplicative_4637_);
lean_dec(v___x_4636_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4698_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v_toFunctor_4641_; lean_object* v_toSeq_4642_; lean_object* v_toSeqLeft_4643_; lean_object* v_toSeqRight_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4696_; 
v_toFunctor_4641_ = lean_ctor_get(v_toApplicative_4637_, 0);
v_toSeq_4642_ = lean_ctor_get(v_toApplicative_4637_, 2);
v_toSeqLeft_4643_ = lean_ctor_get(v_toApplicative_4637_, 3);
v_toSeqRight_4644_ = lean_ctor_get(v_toApplicative_4637_, 4);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_toApplicative_4637_);
if (v_isSharedCheck_4696_ == 0)
{
lean_object* v_unused_4697_; 
v_unused_4697_ = lean_ctor_get(v_toApplicative_4637_, 1);
lean_dec(v_unused_4697_);
v___x_4646_ = v_toApplicative_4637_;
v_isShared_4647_ = v_isSharedCheck_4696_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_toSeqRight_4644_);
lean_inc(v_toSeqLeft_4643_);
lean_inc(v_toSeq_4642_);
lean_inc(v_toFunctor_4641_);
lean_dec(v_toApplicative_4637_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4696_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___f_4648_; lean_object* v___f_4649_; lean_object* v___f_4650_; lean_object* v___f_4651_; lean_object* v___x_4652_; lean_object* v___f_4653_; lean_object* v___f_4654_; lean_object* v___f_4655_; lean_object* v___x_4657_; 
v___f_4648_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4649_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref(v_toFunctor_4641_);
v___f_4650_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4650_, 0, v_toFunctor_4641_);
v___f_4651_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4651_, 0, v_toFunctor_4641_);
v___x_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4652_, 0, v___f_4650_);
lean_ctor_set(v___x_4652_, 1, v___f_4651_);
v___f_4653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4653_, 0, v_toSeqRight_4644_);
v___f_4654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4654_, 0, v_toSeqLeft_4643_);
v___f_4655_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4655_, 0, v_toSeq_4642_);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 4, v___f_4653_);
lean_ctor_set(v___x_4646_, 3, v___f_4654_);
lean_ctor_set(v___x_4646_, 2, v___f_4655_);
lean_ctor_set(v___x_4646_, 1, v___f_4648_);
lean_ctor_set(v___x_4646_, 0, v___x_4652_);
v___x_4657_ = v___x_4646_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v___f_4648_);
lean_ctor_set(v_reuseFailAlloc_4695_, 2, v___f_4655_);
lean_ctor_set(v_reuseFailAlloc_4695_, 3, v___f_4654_);
lean_ctor_set(v_reuseFailAlloc_4695_, 4, v___f_4653_);
v___x_4657_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4659_; 
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 1, v___f_4649_);
lean_ctor_set(v___x_4639_, 0, v___x_4657_);
v___x_4659_ = v___x_4639_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v___f_4649_);
v___x_4659_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4660_; lean_object* v_toApplicative_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4692_; 
v___x_4660_ = l_ReaderT_instMonad___redArg(v___x_4659_);
v_toApplicative_4661_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4692_ == 0)
{
lean_object* v_unused_4693_; 
v_unused_4693_ = lean_ctor_get(v___x_4660_, 1);
lean_dec(v_unused_4693_);
v___x_4663_ = v___x_4660_;
v_isShared_4664_ = v_isSharedCheck_4692_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_toApplicative_4661_);
lean_dec(v___x_4660_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4692_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v_toFunctor_4665_; lean_object* v_toSeq_4666_; lean_object* v_toSeqLeft_4667_; lean_object* v_toSeqRight_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4690_; 
v_toFunctor_4665_ = lean_ctor_get(v_toApplicative_4661_, 0);
v_toSeq_4666_ = lean_ctor_get(v_toApplicative_4661_, 2);
v_toSeqLeft_4667_ = lean_ctor_get(v_toApplicative_4661_, 3);
v_toSeqRight_4668_ = lean_ctor_get(v_toApplicative_4661_, 4);
v_isSharedCheck_4690_ = !lean_is_exclusive(v_toApplicative_4661_);
if (v_isSharedCheck_4690_ == 0)
{
lean_object* v_unused_4691_; 
v_unused_4691_ = lean_ctor_get(v_toApplicative_4661_, 1);
lean_dec(v_unused_4691_);
v___x_4670_ = v_toApplicative_4661_;
v_isShared_4671_ = v_isSharedCheck_4690_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_toSeqRight_4668_);
lean_inc(v_toSeqLeft_4667_);
lean_inc(v_toSeq_4666_);
lean_inc(v_toFunctor_4665_);
lean_dec(v_toApplicative_4661_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4690_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___f_4672_; lean_object* v___f_4673_; lean_object* v___f_4674_; lean_object* v___f_4675_; lean_object* v___x_4676_; lean_object* v___f_4677_; lean_object* v___f_4678_; lean_object* v___f_4679_; lean_object* v___x_4681_; 
v___f_4672_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4673_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4665_);
v___f_4674_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4674_, 0, v_toFunctor_4665_);
v___f_4675_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4675_, 0, v_toFunctor_4665_);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___f_4674_);
lean_ctor_set(v___x_4676_, 1, v___f_4675_);
v___f_4677_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4677_, 0, v_toSeqRight_4668_);
v___f_4678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4678_, 0, v_toSeqLeft_4667_);
v___f_4679_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4679_, 0, v_toSeq_4666_);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 4, v___f_4677_);
lean_ctor_set(v___x_4670_, 3, v___f_4678_);
lean_ctor_set(v___x_4670_, 2, v___f_4679_);
lean_ctor_set(v___x_4670_, 1, v___f_4672_);
lean_ctor_set(v___x_4670_, 0, v___x_4676_);
v___x_4681_ = v___x_4670_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4676_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v___f_4672_);
lean_ctor_set(v_reuseFailAlloc_4689_, 2, v___f_4679_);
lean_ctor_set(v_reuseFailAlloc_4689_, 3, v___f_4678_);
lean_ctor_set(v_reuseFailAlloc_4689_, 4, v___f_4677_);
v___x_4681_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_object* v___x_4683_; 
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 1, v___f_4673_);
lean_ctor_set(v___x_4663_, 0, v___x_4681_);
v___x_4683_ = v___x_4663_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4681_);
lean_ctor_set(v_reuseFailAlloc_4688_, 1, v___f_4673_);
v___x_4683_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_1342__overap_4686_; lean_object* v___x_4687_; 
v___x_4684_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4685_ = l_instInhabitedOfMonad___redArg(v___x_4683_, v___x_4684_);
v___x_1342__overap_4686_ = lean_panic_fn(v___x_4685_, v_msg_4630_);
v___x_4687_ = lean_apply_5(v___x_1342__overap_4686_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, lean_box(0));
return v___x_4687_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
return v_res_4706_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4710_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4711_ = lean_unsigned_to_nat(2u);
v___x_4712_ = lean_unsigned_to_nat(89u);
v___x_4713_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4714_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4715_ = l_mkPanicMessageWithDecl(v___x_4714_, v___x_4713_, v___x_4712_, v___x_4711_, v___x_4710_);
return v___x_4715_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4717_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4718_ = lean_unsigned_to_nat(2u);
v___x_4719_ = lean_unsigned_to_nat(90u);
v___x_4720_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4721_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4722_ = l_mkPanicMessageWithDecl(v___x_4721_, v___x_4720_, v___x_4719_, v___x_4718_, v___x_4717_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_inst_4725_, lean_object* v_f_4726_, lean_object* v_positions_4727_, lean_object* v_ys_4728_, lean_object* v_xs_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; 
v___x_4735_ = lean_array_get_size(v_positions_4727_);
v___x_4736_ = lean_array_get_size(v_ys_4728_);
v___x_4737_ = lean_nat_dec_eq(v___x_4735_, v___x_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; lean_object* v___x_4739_; 
lean_dec_ref(v_f_4726_);
lean_dec(v_inst_4725_);
v___x_4738_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4739_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4738_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
return v___x_4739_;
}
else
{
lean_object* v___x_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4740_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4727_);
v___x_4741_ = lean_array_get_size(v_xs_4729_);
v___x_4742_ = lean_nat_dec_eq(v___x_4740_, v___x_4741_);
lean_dec(v___x_4740_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
lean_dec_ref(v_f_4726_);
lean_dec(v_inst_4725_);
v___x_4743_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4744_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4743_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
return v___x_4744_;
}
else
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4745_ = lean_unsigned_to_nat(0u);
v___x_4746_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4747_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_inst_4725_, v_xs_4729_, v_f_4726_, v_ys_4728_, v_positions_4727_, v___x_4745_, v___x_4746_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
return v___x_4747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_inst_4748_, lean_object* v_f_4749_, lean_object* v_positions_4750_, lean_object* v_ys_4751_, lean_object* v_xs_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_inst_4748_, v_f_4749_, v_positions_4750_, v_ys_4751_, v_xs_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec_ref(v_xs_4752_);
lean_dec_ref(v_ys_4751_);
lean_dec_ref(v_positions_4750_);
return v_res_4758_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4760_ = lean_unsigned_to_nat(0u);
v___x_4761_ = l_Lean_Level_ofNat(v___x_4760_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4762_, lean_object* v_positions_4763_, lean_object* v_motives_4764_, uint8_t v_isIndPred_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v_indGroupInst_4774_; lean_object* v___x_4775_; lean_object* v_brecOnUniv_4777_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v___y_4780_; lean_object* v___y_4781_; 
v___x_4771_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4772_ = lean_unsigned_to_nat(0u);
v___x_4773_ = lean_array_get_borrowed(v___x_4771_, v_recArgInfos_4762_, v___x_4772_);
v_indGroupInst_4774_ = lean_ctor_get(v___x_4773_, 4);
v___x_4775_ = l_Lean_instInhabitedExpr;
if (v_isIndPred_4765_ == 0)
{
lean_object* v___f_4818_; lean_object* v_motive_4819_; lean_object* v___x_4820_; 
v___f_4818_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v_motive_4819_ = lean_array_get_borrowed(v___x_4775_, v_motives_4764_, v___x_4772_);
lean_inc(v_a_4769_);
lean_inc_ref(v_a_4768_);
lean_inc(v_a_4767_);
lean_inc_ref(v_a_4766_);
lean_inc(v_motive_4819_);
v___x_4820_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___redArg(v_motive_4819_, v___f_4818_, v_isIndPred_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4821_);
lean_dec_ref(v___x_4820_);
v_brecOnUniv_4777_ = v_a_4821_;
v___y_4778_ = v_a_4766_;
v___y_4779_ = v_a_4767_;
v___y_4780_ = v_a_4768_;
v___y_4781_ = v_a_4769_;
goto v___jp_4776_;
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
v_a_4822_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4820_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4820_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_object* v___x_4830_; 
v___x_4830_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4777_ = v___x_4830_;
v___y_4778_ = v_a_4766_;
v___y_4779_ = v_a_4767_;
v___y_4780_ = v_a_4768_;
v___y_4781_ = v_a_4769_;
goto v___jp_4776_;
}
v___jp_4776_:
{
lean_object* v_toIndGroupInfo_4782_; lean_object* v_levels_4783_; lean_object* v_params_4784_; lean_object* v___x_4785_; lean_object* v_brecOnCons_4786_; lean_object* v_brecOnAux_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v_toIndGroupInfo_4782_ = lean_ctor_get(v_indGroupInst_4774_, 0);
v_levels_4783_ = lean_ctor_get(v_indGroupInst_4774_, 1);
v_params_4784_ = lean_ctor_get(v_indGroupInst_4774_, 2);
v___x_4785_ = lean_box(v_isIndPred_4765_);
lean_inc(v_levels_4783_);
lean_inc(v_brecOnUniv_4777_);
lean_inc_ref(v_params_4784_);
lean_inc_ref(v_toIndGroupInfo_4782_);
v_brecOnCons_4786_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4786_, 0, v_toIndGroupInfo_4782_);
lean_closure_set(v_brecOnCons_4786_, 1, v_params_4784_);
lean_closure_set(v_brecOnCons_4786_, 2, v___x_4785_);
lean_closure_set(v_brecOnCons_4786_, 3, v_brecOnUniv_4777_);
lean_closure_set(v_brecOnCons_4786_, 4, v_levels_4783_);
lean_inc(v_levels_4783_);
v_brecOnAux_4787_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4782_, v_params_4784_, v_isIndPred_4765_, v_brecOnUniv_4777_, v_levels_4783_, v___x_4772_);
v___x_4788_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4782_);
lean_inc(v___y_4781_);
lean_inc_ref(v___y_4780_);
lean_inc(v___y_4779_);
lean_inc_ref(v___y_4778_);
v___x_4789_ = l_Lean_Meta_inferArgumentTypesN(v___x_4788_, v_brecOnAux_4787_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v___x_4789_);
v___x_4791_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__0));
v___x_4792_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4775_, v___x_4791_, v_positions_4763_, v_a_4790_, v_motives_4764_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v_a_4790_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4801_; 
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4795_ = v___x_4792_;
v_isShared_4796_ = v_isSharedCheck_4801_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4792_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4801_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___f_4797_; lean_object* v___x_4799_; 
v___f_4797_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4797_, 0, v_brecOnCons_4786_);
lean_closure_set(v___f_4797_, 1, v_a_4793_);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 0, v___f_4797_);
v___x_4799_ = v___x_4795_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___f_4797_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
lean_dec_ref(v_brecOnCons_4786_);
v_a_4802_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4792_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4792_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
lean_dec_ref(v_brecOnCons_4786_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
v_a_4810_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4789_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4789_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4831_, lean_object* v_positions_4832_, lean_object* v_motives_4833_, lean_object* v_isIndPred_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
uint8_t v_isIndPred_boxed_4840_; lean_object* v_res_4841_; 
v_isIndPred_boxed_4840_ = lean_unbox(v_isIndPred_4834_);
v_res_4841_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4831_, v_positions_4832_, v_motives_4833_, v_isIndPred_boxed_4840_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
lean_dec_ref(v_motives_4833_);
lean_dec_ref(v_positions_4832_);
lean_dec_ref(v_recArgInfos_4831_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4842_, lean_object* v_msg_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4850_, lean_object* v_msg_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4850_, v_msg_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4858_, lean_object* v_00_u03b1_4859_, lean_object* v_00_u03b2_4860_, lean_object* v_inst_4861_, lean_object* v_f_4862_, lean_object* v_positions_4863_, lean_object* v_ys_4864_, lean_object* v_xs_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
lean_object* v___x_4871_; 
v___x_4871_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_inst_4861_, v_f_4862_, v_positions_4863_, v_ys_4864_, v_xs_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4872_, lean_object* v_00_u03b1_4873_, lean_object* v_00_u03b2_4874_, lean_object* v_inst_4875_, lean_object* v_f_4876_, lean_object* v_positions_4877_, lean_object* v_ys_4878_, lean_object* v_xs_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4872_, v_00_u03b1_4873_, v_00_u03b2_4874_, v_inst_4875_, v_f_4876_, v_positions_4877_, v_ys_4878_, v_xs_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
lean_dec_ref(v_xs_4879_);
lean_dec_ref(v_ys_4878_);
lean_dec_ref(v_positions_4877_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_00_u03b2_4886_, lean_object* v_inst_4887_, lean_object* v_xs_4888_, size_t v_sz_4889_, size_t v_i_4890_, lean_object* v_bs_4891_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(v_inst_4887_, v_xs_4888_, v_sz_4889_, v_i_4890_, v_bs_4891_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4893_, lean_object* v_inst_4894_, lean_object* v_xs_4895_, lean_object* v_sz_4896_, lean_object* v_i_4897_, lean_object* v_bs_4898_){
_start:
{
size_t v_sz_boxed_4899_; size_t v_i_boxed_4900_; lean_object* v_res_4901_; 
v_sz_boxed_4899_ = lean_unbox_usize(v_sz_4896_);
lean_dec(v_sz_4896_);
v_i_boxed_4900_ = lean_unbox_usize(v_i_4897_);
lean_dec(v_i_4897_);
v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_00_u03b2_4893_, v_inst_4894_, v_xs_4895_, v_sz_boxed_4899_, v_i_boxed_4900_, v_bs_4898_);
lean_dec_ref(v_xs_4895_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4902_, lean_object* v_00_u03b3_4903_, lean_object* v_00_u03b2_4904_, lean_object* v_inst_4905_, lean_object* v_xs_4906_, lean_object* v_f_4907_, lean_object* v_as_4908_, lean_object* v_bs_4909_, lean_object* v_i_4910_, lean_object* v_cs_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_inst_4905_, v_xs_4906_, v_f_4907_, v_as_4908_, v_bs_4909_, v_i_4910_, v_cs_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4918_, lean_object* v_00_u03b3_4919_, lean_object* v_00_u03b2_4920_, lean_object* v_inst_4921_, lean_object* v_xs_4922_, lean_object* v_f_4923_, lean_object* v_as_4924_, lean_object* v_bs_4925_, lean_object* v_i_4926_, lean_object* v_cs_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4918_, v_00_u03b3_4919_, v_00_u03b2_4920_, v_inst_4921_, v_xs_4922_, v_f_4923_, v_as_4924_, v_bs_4925_, v_i_4926_, v_cs_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
lean_dec_ref(v_bs_4925_);
lean_dec_ref(v_as_4924_);
lean_dec_ref(v_xs_4922_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(lean_object* v_type_4934_, lean_object* v_maxFVars_x3f_4935_, lean_object* v_k_4936_, uint8_t v_cleanupAnnotations_4937_, uint8_t v_whnfType_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v___f_4944_; lean_object* v___x_4945_; 
v___f_4944_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4944_, 0, v_k_4936_);
v___x_4945_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4934_, v_maxFVars_x3f_4935_, v___f_4944_, v_cleanupAnnotations_4937_, v_whnfType_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4945_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4945_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
v_a_4954_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4945_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4945_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg___boxed(lean_object* v_type_4962_, lean_object* v_maxFVars_x3f_4963_, lean_object* v_k_4964_, lean_object* v_cleanupAnnotations_4965_, lean_object* v_whnfType_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4972_; uint8_t v_whnfType_boxed_4973_; lean_object* v_res_4974_; 
v_cleanupAnnotations_boxed_4972_ = lean_unbox(v_cleanupAnnotations_4965_);
v_whnfType_boxed_4973_ = lean_unbox(v_whnfType_4966_);
v_res_4974_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4962_, v_maxFVars_x3f_4963_, v_k_4964_, v_cleanupAnnotations_boxed_4972_, v_whnfType_boxed_4973_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_00_u03b1_4975_, lean_object* v_type_4976_, lean_object* v_maxFVars_x3f_4977_, lean_object* v_k_4978_, uint8_t v_cleanupAnnotations_4979_, uint8_t v_whnfType_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4976_, v_maxFVars_x3f_4977_, v_k_4978_, v_cleanupAnnotations_4979_, v_whnfType_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_00_u03b1_4987_, lean_object* v_type_4988_, lean_object* v_maxFVars_x3f_4989_, lean_object* v_k_4990_, lean_object* v_cleanupAnnotations_4991_, lean_object* v_whnfType_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4998_; uint8_t v_whnfType_boxed_4999_; lean_object* v_res_5000_; 
v_cleanupAnnotations_boxed_4998_ = lean_unbox(v_cleanupAnnotations_4991_);
v_whnfType_boxed_4999_ = lean_unbox(v_whnfType_4992_);
v_res_5000_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_00_u03b1_4987_, v_type_4988_, v_maxFVars_x3f_4989_, v_k_4990_, v_cleanupAnnotations_boxed_4998_, v_whnfType_boxed_4999_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_5001_, lean_object* v_e_5002_){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5003_ = l_Lean_indentD(v_e_5002_);
v___x_5004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5004_, 0, v___x_5001_);
lean_ctor_set(v___x_5004_, 1, v___x_5003_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_5005_, lean_object* v_x_5006_, lean_object* v_brecOnType_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_5005_, v_brecOnType_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_5014_, lean_object* v_x_5015_, lean_object* v_brecOnType_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_5014_, v_x_5015_, v_brecOnType_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
lean_dec_ref(v_x_5015_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_5023_, lean_object* v_as_5024_, size_t v_sz_5025_, size_t v_i_5026_, lean_object* v_b_5027_){
_start:
{
uint8_t v___x_5029_; 
v___x_5029_ = lean_usize_dec_lt(v_i_5026_, v_sz_5025_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5030_; 
lean_dec_ref(v_a_5023_);
v___x_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5030_, 0, v_b_5027_);
return v___x_5030_;
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5032_; size_t v___x_5033_; size_t v___x_5034_; 
v_a_5031_ = lean_array_uget_borrowed(v_as_5024_, v_i_5026_);
lean_inc_ref(v_a_5023_);
v___x_5032_ = lean_array_set(v_b_5027_, v_a_5031_, v_a_5023_);
v___x_5033_ = ((size_t)1ULL);
v___x_5034_ = lean_usize_add(v_i_5026_, v___x_5033_);
v_i_5026_ = v___x_5034_;
v_b_5027_ = v___x_5032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_5036_, lean_object* v_as_5037_, lean_object* v_sz_5038_, lean_object* v_i_5039_, lean_object* v_b_5040_, lean_object* v___y_5041_){
_start:
{
size_t v_sz_boxed_5042_; size_t v_i_boxed_5043_; lean_object* v_res_5044_; 
v_sz_boxed_5042_ = lean_unbox_usize(v_sz_5038_);
lean_dec(v_sz_5038_);
v_i_boxed_5043_ = lean_unbox_usize(v_i_5039_);
lean_dec(v_i_5039_);
v_res_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_5036_, v_as_5037_, v_sz_boxed_5042_, v_i_boxed_5043_, v_b_5040_);
lean_dec_ref(v_as_5037_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(lean_object* v_as_5045_, size_t v_sz_5046_, size_t v_i_5047_, lean_object* v_b_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
uint8_t v___x_5054_; 
v___x_5054_ = lean_usize_dec_lt(v_i_5047_, v_sz_5046_);
if (v___x_5054_ == 0)
{
lean_object* v___x_5055_; 
v___x_5055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5055_, 0, v_b_5048_);
return v___x_5055_;
}
else
{
lean_object* v_snd_5056_; lean_object* v_fst_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5101_; 
v_snd_5056_ = lean_ctor_get(v_b_5048_, 1);
v_fst_5057_ = lean_ctor_get(v_b_5048_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v_b_5048_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5059_ = v_b_5048_;
v_isShared_5060_ = v_isSharedCheck_5101_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_snd_5056_);
lean_inc(v_fst_5057_);
lean_dec(v_b_5048_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5101_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v_array_5061_; lean_object* v_start_5062_; lean_object* v_stop_5063_; uint8_t v___x_5064_; 
v_array_5061_ = lean_ctor_get(v_snd_5056_, 0);
v_start_5062_ = lean_ctor_get(v_snd_5056_, 1);
v_stop_5063_ = lean_ctor_get(v_snd_5056_, 2);
v___x_5064_ = lean_nat_dec_lt(v_start_5062_, v_stop_5063_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5066_; 
if (v_isShared_5060_ == 0)
{
v___x_5066_ = v___x_5059_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_fst_5057_);
lean_ctor_set(v_reuseFailAlloc_5068_, 1, v_snd_5056_);
v___x_5066_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
return v___x_5067_;
}
}
else
{
lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5097_; 
lean_inc(v_stop_5063_);
lean_inc(v_start_5062_);
lean_inc_ref(v_array_5061_);
v_isSharedCheck_5097_ = !lean_is_exclusive(v_snd_5056_);
if (v_isSharedCheck_5097_ == 0)
{
lean_object* v_unused_5098_; lean_object* v_unused_5099_; lean_object* v_unused_5100_; 
v_unused_5098_ = lean_ctor_get(v_snd_5056_, 2);
lean_dec(v_unused_5098_);
v_unused_5099_ = lean_ctor_get(v_snd_5056_, 1);
lean_dec(v_unused_5099_);
v_unused_5100_ = lean_ctor_get(v_snd_5056_, 0);
lean_dec(v_unused_5100_);
v___x_5070_ = v_snd_5056_;
v_isShared_5071_ = v_isSharedCheck_5097_;
goto v_resetjp_5069_;
}
else
{
lean_dec(v_snd_5056_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5097_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v_a_5072_; lean_object* v___x_5073_; size_t v_sz_5074_; size_t v___x_5075_; lean_object* v___x_5076_; 
v_a_5072_ = lean_array_uget_borrowed(v_as_5045_, v_i_5047_);
v___x_5073_ = lean_array_fget_borrowed(v_array_5061_, v_start_5062_);
v_sz_5074_ = lean_array_size(v___x_5073_);
v___x_5075_ = ((size_t)0ULL);
lean_inc(v_a_5072_);
v___x_5076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_5072_, v___x_5073_, v_sz_5074_, v___x_5075_, v_fst_5057_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5081_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref(v___x_5076_);
v___x_5078_ = lean_unsigned_to_nat(1u);
v___x_5079_ = lean_nat_add(v_start_5062_, v___x_5078_);
lean_dec(v_start_5062_);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 1, v___x_5079_);
v___x_5081_ = v___x_5070_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_array_5061_);
lean_ctor_set(v_reuseFailAlloc_5088_, 1, v___x_5079_);
lean_ctor_set(v_reuseFailAlloc_5088_, 2, v_stop_5063_);
v___x_5081_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
lean_object* v___x_5083_; 
if (v_isShared_5060_ == 0)
{
lean_ctor_set(v___x_5059_, 1, v___x_5081_);
lean_ctor_set(v___x_5059_, 0, v_a_5077_);
v___x_5083_ = v___x_5059_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5077_);
lean_ctor_set(v_reuseFailAlloc_5087_, 1, v___x_5081_);
v___x_5083_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
size_t v___x_5084_; size_t v___x_5085_; 
v___x_5084_ = ((size_t)1ULL);
v___x_5085_ = lean_usize_add(v_i_5047_, v___x_5084_);
v_i_5047_ = v___x_5085_;
v_b_5048_ = v___x_5083_;
goto _start;
}
}
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
lean_del_object(v___x_5070_);
lean_dec(v_stop_5063_);
lean_dec(v_start_5062_);
lean_dec_ref(v_array_5061_);
lean_del_object(v___x_5059_);
v_a_5089_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___x_5076_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5076_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2___boxed(lean_object* v_as_5102_, lean_object* v_sz_5103_, lean_object* v_i_5104_, lean_object* v_b_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
size_t v_sz_boxed_5111_; size_t v_i_boxed_5112_; lean_object* v_res_5113_; 
v_sz_boxed_5111_ = lean_unbox_usize(v_sz_5103_);
lean_dec(v_sz_5103_);
v_i_boxed_5112_ = lean_unbox_usize(v_i_5104_);
lean_dec(v_i_5104_);
v_res_5113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_as_5102_, v_sz_boxed_5111_, v_i_boxed_5112_, v_b_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
lean_dec(v___y_5109_);
lean_dec_ref(v___y_5108_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
lean_dec_ref(v_as_5102_);
return v_res_5113_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5115_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_5116_ = l_Lean_stringToMessageData(v___x_5115_);
return v___x_5116_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_5117_; lean_object* v___f_5118_; 
v___x_5117_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_5118_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_5118_, 0, v___x_5117_);
return v___f_5118_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5119_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_5120_ = l_Lean_Expr_sort___override(v___x_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_5121_, lean_object* v_positions_5122_, lean_object* v_brecOnConst_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v_recArgInfo_5131_; lean_object* v_indicesPos_5132_; lean_object* v_indIdx_5133_; lean_object* v_brecOn_5134_; lean_object* v___f_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5129_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_5130_ = lean_unsigned_to_nat(0u);
v_recArgInfo_5131_ = lean_array_get_borrowed(v___x_5129_, v_recArgInfos_5121_, v___x_5130_);
v_indicesPos_5132_ = lean_ctor_get(v_recArgInfo_5131_, 3);
v_indIdx_5133_ = lean_ctor_get(v_recArgInfo_5131_, 5);
lean_inc(v_indIdx_5133_);
v_brecOn_5134_ = lean_apply_1(v_brecOnConst_5123_, v_indIdx_5133_);
v___f_5135_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
lean_inc_ref(v_brecOn_5134_);
v___x_5136_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_5136_, 0, v_brecOn_5134_);
lean_inc(v_a_5127_);
lean_inc_ref(v_a_5126_);
lean_inc(v_a_5125_);
lean_inc_ref(v_a_5124_);
v___x_5137_ = l_Lean_Meta_mapErrorImp___redArg(v___x_5136_, v___f_5135_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v___x_5138_; 
lean_dec_ref(v___x_5137_);
lean_inc(v_a_5127_);
lean_inc_ref(v_a_5126_);
lean_inc(v_a_5125_);
lean_inc_ref(v_a_5124_);
v___x_5138_ = lean_infer_type(v_brecOn_5134_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; lean_object* v_numTypeFormers_5140_; lean_object* v___f_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; uint8_t v___x_5146_; lean_object* v___x_5147_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_a_5139_);
lean_dec_ref(v___x_5138_);
v_numTypeFormers_5140_ = lean_array_get_size(v_positions_5122_);
v___f_5141_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_5141_, 0, v_numTypeFormers_5140_);
v___x_5142_ = lean_array_get_size(v_indicesPos_5132_);
v___x_5143_ = lean_unsigned_to_nat(1u);
v___x_5144_ = lean_nat_add(v___x_5142_, v___x_5143_);
v___x_5145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5144_);
v___x_5146_ = 0;
lean_inc(v_a_5127_);
lean_inc_ref(v_a_5126_);
lean_inc(v_a_5125_);
lean_inc_ref(v_a_5124_);
v___x_5147_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_a_5139_, v___x_5145_, v___f_5141_, v___x_5146_, v___x_5146_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; size_t v_sz_5154_; size_t v___x_5155_; lean_object* v___x_5156_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_a_5148_);
lean_dec_ref(v___x_5147_);
v___x_5149_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_5122_);
v___x_5150_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_5151_ = lean_mk_array(v___x_5149_, v___x_5150_);
v___x_5152_ = l_Array_toSubarray___redArg(v_positions_5122_, v___x_5130_, v_numTypeFormers_5140_);
v___x_5153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5151_);
lean_ctor_set(v___x_5153_, 1, v___x_5152_);
v_sz_5154_ = lean_array_size(v_a_5148_);
v___x_5155_ = ((size_t)0ULL);
v___x_5156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_a_5148_, v_sz_5154_, v___x_5155_, v___x_5153_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec(v_a_5148_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5165_; 
v_a_5157_ = lean_ctor_get(v___x_5156_, 0);
v_isSharedCheck_5165_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5165_ == 0)
{
v___x_5159_ = v___x_5156_;
v_isShared_5160_ = v_isSharedCheck_5165_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5156_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5165_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v_fst_5161_; lean_object* v___x_5163_; 
v_fst_5161_ = lean_ctor_get(v_a_5157_, 0);
lean_inc(v_fst_5161_);
lean_dec(v_a_5157_);
if (v_isShared_5160_ == 0)
{
lean_ctor_set(v___x_5159_, 0, v_fst_5161_);
v___x_5163_ = v___x_5159_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_fst_5161_);
v___x_5163_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
return v___x_5163_;
}
}
}
else
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5173_; 
v_a_5166_ = lean_ctor_get(v___x_5156_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5168_ = v___x_5156_;
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v___x_5156_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5171_; 
if (v_isShared_5169_ == 0)
{
v___x_5171_ = v___x_5168_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
return v___x_5171_;
}
}
}
}
else
{
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec_ref(v_positions_5122_);
return v___x_5147_;
}
}
else
{
lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5181_; 
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec_ref(v_positions_5122_);
v_a_5174_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5176_ = v___x_5138_;
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_dec(v___x_5138_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
lean_object* v___x_5179_; 
if (v_isShared_5177_ == 0)
{
v___x_5179_ = v___x_5176_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5174_);
v___x_5179_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
return v___x_5179_;
}
}
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec_ref(v_brecOn_5134_);
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec_ref(v_positions_5122_);
v_a_5182_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5137_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5137_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_5190_, lean_object* v_positions_5191_, lean_object* v_brecOnConst_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_5190_, v_positions_5191_, v_brecOnConst_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
lean_dec_ref(v_recArgInfos_5190_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_5199_, lean_object* v_as_5200_, size_t v_sz_5201_, size_t v_i_5202_, lean_object* v_b_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v___x_5209_; 
v___x_5209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_5199_, v_as_5200_, v_sz_5201_, v_i_5202_, v_b_5203_);
return v___x_5209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_5210_, lean_object* v_as_5211_, lean_object* v_sz_5212_, lean_object* v_i_5213_, lean_object* v_b_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
size_t v_sz_boxed_5220_; size_t v_i_boxed_5221_; lean_object* v_res_5222_; 
v_sz_boxed_5220_ = lean_unbox_usize(v_sz_5212_);
lean_dec(v_sz_5212_);
v_i_boxed_5221_ = lean_unbox_usize(v_i_5213_);
lean_dec(v_i_5213_);
v_res_5222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_5210_, v_as_5211_, v_sz_boxed_5220_, v_i_boxed_5221_, v_b_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec_ref(v_as_5211_);
return v_res_5222_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_5223_, lean_object* v_a_5224_){
_start:
{
if (lean_obj_tag(v_a_5223_) == 0)
{
lean_object* v___x_5225_; 
v___x_5225_ = l_List_reverse___redArg(v_a_5224_);
return v___x_5225_;
}
else
{
lean_object* v_head_5226_; lean_object* v_tail_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5238_; 
v_head_5226_ = lean_ctor_get(v_a_5223_, 0);
v_tail_5227_ = lean_ctor_get(v_a_5223_, 1);
v_isSharedCheck_5238_ = !lean_is_exclusive(v_a_5223_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5229_ = v_a_5223_;
v_isShared_5230_ = v_isSharedCheck_5238_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_tail_5227_);
lean_inc(v_head_5226_);
lean_dec(v_a_5223_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5238_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5235_; 
v___x_5231_ = l_Nat_reprFast(v_head_5226_);
v___x_5232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
v___x_5233_ = l_Lean_MessageData_ofFormat(v___x_5232_);
if (v_isShared_5230_ == 0)
{
lean_ctor_set(v___x_5229_, 1, v_a_5224_);
lean_ctor_set(v___x_5229_, 0, v___x_5233_);
v___x_5235_ = v___x_5229_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5233_);
lean_ctor_set(v_reuseFailAlloc_5237_, 1, v_a_5224_);
v___x_5235_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
v_a_5223_ = v_tail_5227_;
v_a_5224_ = v___x_5235_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_5239_, lean_object* v_a_5240_){
_start:
{
if (lean_obj_tag(v_a_5239_) == 0)
{
lean_object* v___x_5241_; 
v___x_5241_ = l_List_reverse___redArg(v_a_5240_);
return v___x_5241_;
}
else
{
lean_object* v_head_5242_; lean_object* v_tail_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5255_; 
v_head_5242_ = lean_ctor_get(v_a_5239_, 0);
v_tail_5243_ = lean_ctor_get(v_a_5239_, 1);
v_isSharedCheck_5255_ = !lean_is_exclusive(v_a_5239_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5245_ = v_a_5239_;
v_isShared_5246_ = v_isSharedCheck_5255_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_tail_5243_);
lean_inc(v_head_5242_);
lean_dec(v_a_5239_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5255_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5252_; 
v___x_5247_ = lean_array_to_list(v_head_5242_);
v___x_5248_ = lean_box(0);
v___x_5249_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_5247_, v___x_5248_);
v___x_5250_ = l_Lean_MessageData_ofList(v___x_5249_);
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 1, v_a_5240_);
lean_ctor_set(v___x_5245_, 0, v___x_5250_);
v___x_5252_ = v___x_5245_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5250_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v_a_5240_);
v___x_5252_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
v_a_5239_ = v_tail_5243_;
v_a_5240_ = v___x_5252_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_5256_, lean_object* v_v_5257_, lean_object* v_i_5258_){
_start:
{
lean_object* v___x_5259_; uint8_t v___x_5260_; 
v___x_5259_ = lean_array_get_size(v_xs_5256_);
v___x_5260_ = lean_nat_dec_lt(v_i_5258_, v___x_5259_);
if (v___x_5260_ == 0)
{
lean_object* v___x_5261_; 
lean_dec(v_i_5258_);
v___x_5261_ = lean_box(0);
return v___x_5261_;
}
else
{
lean_object* v___x_5262_; uint8_t v___x_5263_; 
v___x_5262_ = lean_array_fget_borrowed(v_xs_5256_, v_i_5258_);
v___x_5263_ = lean_nat_dec_eq(v___x_5262_, v_v_5257_);
if (v___x_5263_ == 0)
{
lean_object* v___x_5264_; lean_object* v___x_5265_; 
v___x_5264_ = lean_unsigned_to_nat(1u);
v___x_5265_ = lean_nat_add(v_i_5258_, v___x_5264_);
lean_dec(v_i_5258_);
v_i_5258_ = v___x_5265_;
goto _start;
}
else
{
lean_object* v___x_5267_; 
v___x_5267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5267_, 0, v_i_5258_);
return v___x_5267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_5268_, lean_object* v_v_5269_, lean_object* v_i_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_5268_, v_v_5269_, v_i_5270_);
lean_dec(v_v_5269_);
lean_dec_ref(v_xs_5268_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_5272_, lean_object* v_v_5273_){
_start:
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5274_ = lean_unsigned_to_nat(0u);
v___x_5275_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_5272_, v_v_5273_, v___x_5274_);
return v___x_5275_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_5276_, lean_object* v_v_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_5276_, v_v_5277_);
lean_dec(v_v_5277_);
lean_dec_ref(v_xs_5276_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_5282_, lean_object* v_as_5283_, size_t v_sz_5284_, size_t v_i_5285_, lean_object* v_b_5286_){
_start:
{
uint8_t v___x_5287_; 
v___x_5287_ = lean_usize_dec_lt(v_i_5285_, v_sz_5284_);
if (v___x_5287_ == 0)
{
return v_b_5286_;
}
else
{
lean_object* v___x_5288_; lean_object* v_a_5289_; lean_object* v___x_5290_; 
lean_dec_ref(v_b_5286_);
v___x_5288_ = lean_box(0);
v_a_5289_ = lean_array_uget_borrowed(v_as_5283_, v_i_5285_);
v___x_5290_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_5289_, v_fnIdx_5282_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v___x_5291_; size_t v___x_5292_; size_t v___x_5293_; 
v___x_5291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_5292_ = ((size_t)1ULL);
v___x_5293_ = lean_usize_add(v_i_5285_, v___x_5292_);
v_i_5285_ = v___x_5293_;
v_b_5286_ = v___x_5291_;
goto _start;
}
else
{
lean_object* v_val_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5306_; 
v_val_5295_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5297_ = v___x_5290_;
v_isShared_5298_ = v_isSharedCheck_5306_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_val_5295_);
lean_dec(v___x_5290_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5306_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5302_; 
v___x_5299_ = lean_array_get_size(v_a_5289_);
v___x_5300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5300_, 0, v___x_5299_);
lean_ctor_set(v___x_5300_, 1, v_val_5295_);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v___x_5300_);
v___x_5302_ = v___x_5297_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v___x_5300_);
v___x_5302_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5303_, 0, v___x_5302_);
v___x_5304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5304_, 0, v___x_5303_);
lean_ctor_set(v___x_5304_, 1, v___x_5288_);
return v___x_5304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_5307_, lean_object* v_as_5308_, lean_object* v_sz_5309_, lean_object* v_i_5310_, lean_object* v_b_5311_){
_start:
{
size_t v_sz_boxed_5312_; size_t v_i_boxed_5313_; lean_object* v_res_5314_; 
v_sz_boxed_5312_ = lean_unbox_usize(v_sz_5309_);
lean_dec(v_sz_5309_);
v_i_boxed_5313_ = lean_unbox_usize(v_i_5310_);
lean_dec(v_i_5310_);
v_res_5314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5307_, v_as_5308_, v_sz_boxed_5312_, v_i_boxed_5313_, v_b_5311_);
lean_dec_ref(v_as_5308_);
lean_dec(v_fnIdx_5307_);
return v_res_5314_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___x_5316_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_5317_ = l_Lean_stringToMessageData(v___x_5316_);
return v___x_5317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_5318_, lean_object* v_positions_5319_, lean_object* v_fnIdx_5320_, lean_object* v_brecOnConst_5321_, lean_object* v_packedFArgs_5322_, lean_object* v_funTypes_5323_, lean_object* v_ys_5324_, lean_object* v___value_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
lean_object* v___y_5332_; lean_object* v___y_5333_; lean_object* v___y_5334_; lean_object* v___y_5335_; lean_object* v___x_5349_; lean_object* v_fst_5350_; lean_object* v_snd_5351_; lean_object* v___x_5352_; size_t v_sz_5353_; size_t v___x_5354_; lean_object* v___x_5355_; lean_object* v_fst_5356_; 
lean_inc_ref(v_ys_5324_);
lean_inc_ref(v_recArgInfo_5318_);
v___x_5349_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_5318_, v_ys_5324_);
v_fst_5350_ = lean_ctor_get(v___x_5349_, 0);
lean_inc(v_fst_5350_);
v_snd_5351_ = lean_ctor_get(v___x_5349_, 1);
lean_inc(v_snd_5351_);
lean_dec_ref(v___x_5349_);
v___x_5352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5353_ = lean_array_size(v_positions_5319_);
v___x_5354_ = ((size_t)0ULL);
v___x_5355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5320_, v_positions_5319_, v_sz_5353_, v___x_5354_, v___x_5352_);
v_fst_5356_ = lean_ctor_get(v___x_5355_, 0);
lean_inc(v_fst_5356_);
lean_dec_ref(v___x_5355_);
if (lean_obj_tag(v_fst_5356_) == 0)
{
lean_dec(v_snd_5351_);
lean_dec(v_fst_5350_);
lean_dec_ref(v_ys_5324_);
lean_dec_ref(v_brecOnConst_5321_);
lean_dec_ref(v_recArgInfo_5318_);
v___y_5332_ = v___y_5326_;
v___y_5333_ = v___y_5327_;
v___y_5334_ = v___y_5328_;
v___y_5335_ = v___y_5329_;
goto v___jp_5331_;
}
else
{
lean_object* v_val_5357_; 
v_val_5357_ = lean_ctor_get(v_fst_5356_, 0);
lean_inc(v_val_5357_);
lean_dec_ref(v_fst_5356_);
if (lean_obj_tag(v_val_5357_) == 1)
{
lean_object* v_val_5358_; lean_object* v_fst_5359_; lean_object* v_snd_5360_; lean_object* v_indIdx_5361_; lean_object* v_brecOn_5362_; lean_object* v_brecOn_5363_; lean_object* v_brecOn_5364_; lean_object* v___x_5365_; 
lean_dec(v_fnIdx_5320_);
lean_dec_ref(v_positions_5319_);
v_val_5358_ = lean_ctor_get(v_val_5357_, 0);
lean_inc(v_val_5358_);
lean_dec_ref(v_val_5357_);
v_fst_5359_ = lean_ctor_get(v_val_5358_, 0);
lean_inc(v_fst_5359_);
v_snd_5360_ = lean_ctor_get(v_val_5358_, 1);
lean_inc(v_snd_5360_);
lean_dec(v_val_5358_);
v_indIdx_5361_ = lean_ctor_get(v_recArgInfo_5318_, 5);
lean_inc(v_indIdx_5361_);
lean_dec_ref(v_recArgInfo_5318_);
v_brecOn_5362_ = lean_apply_1(v_brecOnConst_5321_, v_indIdx_5361_);
v_brecOn_5363_ = l_Lean_mkAppN(v_brecOn_5362_, v_fst_5350_);
lean_dec(v_fst_5350_);
v_brecOn_5364_ = l_Lean_mkAppN(v_brecOn_5363_, v_packedFArgs_5322_);
lean_inc(v___y_5329_);
lean_inc_ref(v___y_5328_);
lean_inc(v___y_5327_);
lean_inc_ref(v___y_5326_);
v___x_5365_ = l_Lean_Meta_PProdN_projM(v_fst_5359_, v_snd_5360_, v_brecOn_5364_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
lean_dec(v_snd_5360_);
lean_dec(v_fst_5359_);
if (lean_obj_tag(v___x_5365_) == 0)
{
lean_object* v_a_5366_; lean_object* v___x_5367_; uint8_t v___x_5368_; uint8_t v___x_5369_; lean_object* v___x_5370_; 
v_a_5366_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5366_);
lean_dec_ref(v___x_5365_);
v___x_5367_ = l_Lean_mkAppN(v_a_5366_, v_snd_5351_);
lean_dec(v_snd_5351_);
v___x_5368_ = 1;
v___x_5369_ = 1;
v___x_5370_ = l_Lean_Meta_mkLetFVars(v_funTypes_5323_, v___x_5367_, v___x_5368_, v___x_5368_, v___x_5369_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
if (lean_obj_tag(v___x_5370_) == 0)
{
lean_object* v_a_5371_; uint8_t v___x_5372_; lean_object* v___x_5373_; 
v_a_5371_ = lean_ctor_get(v___x_5370_, 0);
lean_inc(v_a_5371_);
lean_dec_ref(v___x_5370_);
v___x_5372_ = 0;
v___x_5373_ = l_Lean_Meta_mkLambdaFVars(v_ys_5324_, v_a_5371_, v___x_5372_, v___x_5368_, v___x_5372_, v___x_5368_, v___x_5369_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec_ref(v_ys_5324_);
return v___x_5373_;
}
else
{
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec_ref(v_ys_5324_);
return v___x_5370_;
}
}
else
{
lean_dec(v_snd_5351_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec_ref(v_ys_5324_);
return v___x_5365_;
}
}
else
{
lean_dec(v_val_5357_);
lean_dec(v_snd_5351_);
lean_dec(v_fst_5350_);
lean_dec_ref(v_ys_5324_);
lean_dec_ref(v_brecOnConst_5321_);
lean_dec_ref(v_recArgInfo_5318_);
v___y_5332_ = v___y_5326_;
v___y_5333_ = v___y_5327_;
v___y_5334_ = v___y_5328_;
v___y_5335_ = v___y_5329_;
goto v___jp_5331_;
}
}
v___jp_5331_:
{
lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5336_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_5337_ = l_Nat_reprFast(v_fnIdx_5320_);
v___x_5338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5337_);
v___x_5339_ = l_Lean_MessageData_ofFormat(v___x_5338_);
v___x_5340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5340_, 0, v___x_5336_);
lean_ctor_set(v___x_5340_, 1, v___x_5339_);
v___x_5341_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_5342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5340_);
lean_ctor_set(v___x_5342_, 1, v___x_5341_);
v___x_5343_ = lean_array_to_list(v_positions_5319_);
v___x_5344_ = lean_box(0);
v___x_5345_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5343_, v___x_5344_);
v___x_5346_ = l_Lean_MessageData_ofList(v___x_5345_);
v___x_5347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5342_);
lean_ctor_set(v___x_5347_, 1, v___x_5346_);
v___x_5348_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5347_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
return v___x_5348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5374_, lean_object* v_positions_5375_, lean_object* v_fnIdx_5376_, lean_object* v_brecOnConst_5377_, lean_object* v_packedFArgs_5378_, lean_object* v_funTypes_5379_, lean_object* v_ys_5380_, lean_object* v___value_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v_res_5387_; 
v_res_5387_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5374_, v_positions_5375_, v_fnIdx_5376_, v_brecOnConst_5377_, v_packedFArgs_5378_, v_funTypes_5379_, v_ys_5380_, v___value_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_);
lean_dec_ref(v___value_5381_);
lean_dec_ref(v_funTypes_5379_);
lean_dec_ref(v_packedFArgs_5378_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5388_, lean_object* v_fnIdx_5389_, lean_object* v_brecOnConst_5390_, lean_object* v_packedFArgs_5391_, lean_object* v_funTypes_5392_, lean_object* v_recArgInfo_5393_, lean_object* v_value_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_){
_start:
{
lean_object* v___f_5400_; uint8_t v___x_5401_; lean_object* v___x_5402_; 
v___f_5400_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5400_, 0, v_recArgInfo_5393_);
lean_closure_set(v___f_5400_, 1, v_positions_5388_);
lean_closure_set(v___f_5400_, 2, v_fnIdx_5389_);
lean_closure_set(v___f_5400_, 3, v_brecOnConst_5390_);
lean_closure_set(v___f_5400_, 4, v_packedFArgs_5391_);
lean_closure_set(v___f_5400_, 5, v_funTypes_5392_);
v___x_5401_ = 0;
v___x_5402_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnConst_spec__1___redArg(v_value_5394_, v___f_5400_, v___x_5401_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_);
return v___x_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5403_, lean_object* v_fnIdx_5404_, lean_object* v_brecOnConst_5405_, lean_object* v_packedFArgs_5406_, lean_object* v_funTypes_5407_, lean_object* v_recArgInfo_5408_, lean_object* v_value_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v_res_5415_; 
v_res_5415_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5403_, v_fnIdx_5404_, v_brecOnConst_5405_, v_packedFArgs_5406_, v_funTypes_5407_, v_recArgInfo_5408_, v_value_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_);
return v_res_5415_;
}
}
lean_object* runtime_initialize_Lean_Util_HasConstCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_BRecOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
