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
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not type correct!"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "initial belowDict for "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__9;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1;
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
lean_dec_ref(v___x_123_);
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
lean_dec_ref(v___x_154_);
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
lean_dec_ref(v_declName_113_);
lean_dec_ref(v_fn_111_);
lean_dec_ref(v_a_110_);
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
lean_dec_ref(v_fn_111_);
lean_dec_ref(v_a_110_);
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
lean_dec_ref(v_fn_111_);
lean_dec_ref(v_a_110_);
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
lean_dec_ref(v_a_110_);
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
lean_dec_ref(v_declName_189_);
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
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
v___x_281_ = lean_apply_7(v_k_273_, v_b_274_, v_c_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, lean_box(0));
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0___boxed(lean_object* v_k_282_, lean_object* v_b_283_, lean_object* v_c_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0(v_k_282_, v_b_283_, v_c_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
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
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
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
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
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
return v___x_496_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
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
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
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
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
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
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
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
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
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
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
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
lean_object* v___x_792_; lean_object* v___f_793_; size_t v_sz_794_; size_t v___x_795_; lean_object* v___x_7880__overap_796_; lean_object* v___x_797_; 
v___x_792_ = lean_array_fget_borrowed(v_array_780_, v_start_781_);
lean_inc(v___x_792_);
v___f_793_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_793_, 0, v___x_792_);
v_sz_794_ = lean_array_size(v_a_767_);
v___x_795_ = ((size_t)0ULL);
v___x_7880__overap_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_766_, v_a_767_, v___f_793_, v_sz_794_, v___x_795_, v_fst_776_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
lean_inc(v___y_771_);
lean_inc_ref(v___y_770_);
v___x_797_ = lean_apply_5(v___x_7880__overap_796_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, lean_box(0));
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
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_837_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__3));
v___x_843_ = l_Lean_stringToMessageData(v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__5));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__9(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__8));
v___x_850_ = l_Lean_stringToMessageData(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_851_, lean_object* v___x_852_, lean_object* v_positions_853_, lean_object* v_a_854_, lean_object* v___x_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v___x_858_, lean_object* v___x_859_, lean_object* v_k_860_, lean_object* v___x_861_, lean_object* v___f_862_, lean_object* v_Cs_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_7908__overap_870_; lean_object* v___x_871_; 
v___x_869_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__0));
lean_inc_ref(v_Cs_863_);
lean_inc_ref(v___x_851_);
v___x_7908__overap_870_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_851_, v___x_852_, v___x_869_, v_positions_853_, v_a_854_, v_Cs_863_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
v___x_871_ = lean_apply_5(v___x_7908__overap_870_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_7911__overap_873_; lean_object* v___x_874_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v___x_871_);
lean_inc(v___x_857_);
lean_inc(v___x_856_);
lean_inc_ref(v___x_855_);
lean_inc_ref(v___x_851_);
v___x_7911__overap_873_ = l_Lean_isTracingEnabledFor___redArg(v___x_851_, v___x_855_, v___x_856_, v___x_857_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
v___x_874_ = lean_apply_5(v___x_7911__overap_873_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; uint8_t v___x_928_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref(v___x_874_);
v___x_876_ = l_Lean_mkAppN(v___x_858_, v_a_872_);
lean_dec(v_a_872_);
v___x_877_ = l_Subarray_copy___redArg(v___x_859_);
v___x_878_ = l_Lean_mkAppN(v___x_876_, v___x_877_);
lean_dec_ref(v___x_877_);
v___x_928_ = lean_unbox(v_a_875_);
lean_dec(v_a_875_);
if (v___x_928_ == 0)
{
v___y_880_ = v___y_864_;
v___y_881_ = v___y_865_;
v___y_882_ = v___y_866_;
v___y_883_ = v___y_867_;
goto v___jp_879_;
}
else
{
lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_toMonadRef_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_7971__overap_947_; lean_object* v___x_948_; 
v___f_929_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2));
v___x_931_ = l_Lean_Core_instMonadQuotationCoreM;
lean_inc(v___x_861_);
v___x_932_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_930_, v___x_861_, v___x_931_);
lean_inc(v___f_862_);
v___x_933_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_929_, v___f_862_, v___x_932_);
v_toMonadRef_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc_ref(v_toMonadRef_934_);
lean_dec_ref(v___x_933_);
v___x_935_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_936_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__6);
lean_inc_ref(v_Cs_863_);
v___x_937_ = lean_array_to_list(v_Cs_863_);
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__7));
v___x_939_ = lean_box(0);
v___x_940_ = l_List_mapTR_loop___redArg(v___x_938_, v___x_937_, v___x_939_);
v___x_941_ = l_Lean_MessageData_ofList(v___x_940_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_936_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__9);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
lean_inc_ref(v___x_878_);
v___x_945_ = l_Lean_indentExpr(v___x_878_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
lean_inc(v___x_857_);
lean_inc_ref(v___x_855_);
lean_inc_ref(v___x_851_);
v___x_7971__overap_947_ = l_Lean_addTrace___redArg(v___x_851_, v___x_855_, v_toMonadRef_934_, v___x_935_, v___x_857_, v___x_946_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
v___x_948_ = lean_apply_5(v___x_7971__overap_947_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
if (lean_obj_tag(v___x_948_) == 0)
{
lean_dec_ref(v___x_948_);
v___y_880_ = v___y_864_;
v___y_881_ = v___y_865_;
v___y_882_ = v___y_866_;
v___y_883_ = v___y_867_;
goto v___jp_879_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v_Cs_863_);
lean_dec(v___f_862_);
lean_dec(v___x_861_);
lean_dec_ref(v_k_860_);
lean_dec(v___x_857_);
lean_dec(v___x_856_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_851_);
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
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
v___jp_879_:
{
lean_object* v___x_884_; 
lean_inc_ref(v___x_878_);
v___x_884_ = l_Lean_Meta_isTypeCorrect(v___x_878_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; uint8_t v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v___x_886_ = lean_unbox(v_a_885_);
lean_dec(v_a_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_7926__overap_887_; lean_object* v___x_888_; 
lean_inc(v___x_857_);
lean_inc_ref(v___x_855_);
lean_inc_ref(v___x_851_);
v___x_7926__overap_887_ = l_Lean_isTracingEnabledFor___redArg(v___x_851_, v___x_855_, v___x_856_, v___x_857_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
v___x_888_ = lean_apply_5(v___x_7926__overap_887_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; uint8_t v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
v___x_890_ = lean_unbox(v_a_889_);
lean_dec(v_a_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v___f_862_);
lean_dec(v___x_861_);
lean_dec(v___x_857_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_851_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
v___x_891_ = lean_apply_7(v_k_860_, v_Cs_863_, v___x_878_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
return v___x_891_;
}
else
{
lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_toMonadRef_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_7938__overap_900_; lean_object* v___x_901_; 
v___f_892_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2));
v___x_894_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_895_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_893_, v___x_861_, v___x_894_);
v___x_896_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_892_, v___f_862_, v___x_895_);
v_toMonadRef_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc_ref(v_toMonadRef_897_);
lean_dec_ref(v___x_896_);
v___x_898_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_899_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4);
v___x_7938__overap_900_ = l_Lean_addTrace___redArg(v___x_851_, v___x_855_, v_toMonadRef_897_, v___x_898_, v___x_857_, v___x_899_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
v___x_901_ = lean_apply_5(v___x_7938__overap_900_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v___x_902_; 
lean_dec_ref(v___x_901_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
v___x_902_ = lean_apply_7(v_k_860_, v_Cs_863_, v___x_878_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
return v___x_902_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v_Cs_863_);
lean_dec_ref(v_k_860_);
v_a_903_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_901_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_901_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v_Cs_863_);
lean_dec(v___f_862_);
lean_dec(v___x_861_);
lean_dec_ref(v_k_860_);
lean_dec(v___x_857_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_851_);
v_a_911_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_888_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_888_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v___x_919_; 
lean_dec(v___f_862_);
lean_dec(v___x_861_);
lean_dec(v___x_857_);
lean_dec(v___x_856_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_851_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
v___x_919_ = lean_apply_7(v_k_860_, v_Cs_863_, v___x_878_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
return v___x_919_;
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v_Cs_863_);
lean_dec(v___f_862_);
lean_dec(v___x_861_);
lean_dec_ref(v_k_860_);
lean_dec(v___x_857_);
lean_dec(v___x_856_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_851_);
v_a_920_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_884_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_884_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v_a_872_);
lean_dec_ref(v_Cs_863_);
lean_dec(v___f_862_);
lean_dec(v___x_861_);
lean_dec_ref(v_k_860_);
lean_dec_ref(v___x_859_);
lean_dec_ref(v___x_858_);
lean_dec(v___x_857_);
lean_dec(v___x_856_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_851_);
v_a_957_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_874_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_874_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v_Cs_863_);
lean_dec(v___f_862_);
lean_dec(v___x_861_);
lean_dec_ref(v_k_860_);
lean_dec_ref(v___x_859_);
lean_dec_ref(v___x_858_);
lean_dec(v___x_857_);
lean_dec(v___x_856_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_851_);
v_a_965_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_871_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_871_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_973_ = _args[0];
lean_object* v___x_974_ = _args[1];
lean_object* v_positions_975_ = _args[2];
lean_object* v_a_976_ = _args[3];
lean_object* v___x_977_ = _args[4];
lean_object* v___x_978_ = _args[5];
lean_object* v___x_979_ = _args[6];
lean_object* v___x_980_ = _args[7];
lean_object* v___x_981_ = _args[8];
lean_object* v_k_982_ = _args[9];
lean_object* v___x_983_ = _args[10];
lean_object* v___f_984_ = _args[11];
lean_object* v_Cs_985_ = _args[12];
lean_object* v___y_986_ = _args[13];
lean_object* v___y_987_ = _args[14];
lean_object* v___y_988_ = _args[15];
lean_object* v___y_989_ = _args[16];
lean_object* v___y_990_ = _args[17];
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_973_, v___x_974_, v_positions_975_, v_a_976_, v___x_977_, v___x_978_, v___x_979_, v___x_980_, v___x_981_, v_k_982_, v___x_983_, v___f_984_, v_Cs_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_991_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(37u);
v___x_993_ = l_Lean_Level_ofNat(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0);
v___x_995_ = l_Lean_Expr_sort___override(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v_positions_1002_, lean_object* v___x_1003_, lean_object* v___f_1004_, lean_object* v___f_1005_, lean_object* v___x_1006_, lean_object* v_numTypeFormers_1007_, lean_object* v___x_1008_, lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_k_1012_, lean_object* v___x_1013_, lean_object* v___f_1014_, lean_object* v_numIndParams_1015_, lean_object* v_a_1016_, lean_object* v_f_1017_, lean_object* v_args_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1158_ = lean_nat_add(v_numIndParams_1015_, v_numTypeFormers_1007_);
v___x_1159_ = lean_array_get_size(v_args_1018_);
v___x_1160_ = lean_nat_dec_lt(v___x_1158_, v___x_1159_);
lean_dec(v___x_1158_);
if (v___x_1160_ == 0)
{
lean_object* v___x_8091__overap_1161_; lean_object* v___x_1162_; 
lean_dec_ref(v_args_1018_);
lean_dec_ref(v_f_1017_);
lean_dec(v_numIndParams_1015_);
lean_dec_ref(v_k_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_numTypeFormers_1007_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v___f_1004_);
lean_dec_ref(v_positions_1002_);
lean_inc(v___x_1010_);
lean_inc_ref(v___x_1008_);
lean_inc_ref(v___x_1003_);
v___x_8091__overap_1161_ = l_Lean_isTracingEnabledFor___redArg(v___x_1003_, v___x_1008_, v___x_1009_, v___x_1010_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
v___x_1162_ = lean_apply_5(v___x_8091__overap_1161_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; uint8_t v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = lean_unbox(v_a_1163_);
lean_dec(v_a_1163_);
if (v___x_1164_ == 0)
{
lean_dec_ref(v_a_1016_);
lean_dec(v___f_1014_);
lean_dec(v___x_1013_);
lean_dec(v___x_1010_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v___x_1003_);
v___y_1145_ = v___y_1019_;
v___y_1146_ = v___y_1020_;
v___y_1147_ = v___y_1021_;
v___y_1148_ = v___y_1022_;
goto v___jp_1144_;
}
else
{
lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_toMonadRef_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_8116__overap_1175_; lean_object* v___x_1176_; 
v___f_1165_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_1166_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2));
v___x_1167_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1168_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1166_, v___x_1013_, v___x_1167_);
v___x_1169_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1165_, v___f_1014_, v___x_1168_);
v_toMonadRef_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc_ref(v_toMonadRef_1170_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1172_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5);
v___x_1173_ = l_Lean_indentExpr(v_a_1016_);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_8116__overap_1175_ = l_Lean_addTrace___redArg(v___x_1003_, v___x_1008_, v_toMonadRef_1170_, v___x_1171_, v___x_1010_, v___x_1174_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
v___x_1176_ = lean_apply_5(v___x_8116__overap_1175_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_dec_ref(v___x_1176_);
v___y_1145_ = v___y_1019_;
v___y_1146_ = v___y_1020_;
v___y_1147_ = v___y_1021_;
v___y_1148_ = v___y_1022_;
goto v___jp_1144_;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_a_1016_);
lean_dec(v___f_1014_);
lean_dec(v___x_1013_);
lean_dec(v___x_1010_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v___x_1003_);
v_a_1185_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1162_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1162_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_dec_ref(v_a_1016_);
v___y_1133_ = v___y_1019_;
v___y_1134_ = v___y_1020_;
v___y_1135_ = v___y_1021_;
v___y_1136_ = v___y_1022_;
goto v___jp_1132_;
}
v___jp_1024_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; size_t v_sz_1038_; size_t v___x_1039_; lean_object* v___x_8017__overap_1040_; lean_object* v___x_1041_; 
v___x_1033_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1);
v___x_1034_ = lean_mk_array(v___y_1028_, v___x_1033_);
v___x_1035_ = lean_array_get_size(v___y_1027_);
v___x_1036_ = l_Array_toSubarray___redArg(v___y_1027_, v___y_1025_, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1034_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v_sz_1038_ = lean_array_size(v_positions_1002_);
v___x_1039_ = ((size_t)0ULL);
lean_inc_ref(v___x_1003_);
v___x_8017__overap_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1003_, v_positions_1002_, v___f_1004_, v_sz_1038_, v___x_1039_, v___x_1037_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
v___x_1041_ = lean_apply_5(v___x_8017__overap_1040_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, lean_box(0));
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v_fst_1043_; size_t v_sz_1044_; lean_object* v___x_8020__overap_1045_; lean_object* v___x_1046_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v___x_1041_);
v_fst_1043_ = lean_ctor_get(v_a_1042_, 0);
lean_inc(v_fst_1043_);
lean_dec(v_a_1042_);
v_sz_1044_ = lean_array_size(v_fst_1043_);
lean_inc_ref(v___x_1003_);
v___x_8020__overap_1045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1003_, v___f_1005_, v_sz_1044_, v___x_1039_, v_fst_1043_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
v___x_1046_ = lean_apply_5(v___x_8020__overap_1045_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, lean_box(0));
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; uint8_t v___x_1048_; lean_object* v___x_8024__overap_1049_; lean_object* v___x_1050_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref(v___x_1046_);
v___x_1048_ = 0;
v___x_8024__overap_1049_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1006_, v___x_1003_, v_a_1047_, v___y_1026_, v___x_1048_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
v___x_1050_ = lean_apply_5(v___x_8024__overap_1049_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, lean_box(0));
return v___x_1050_;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v___x_1003_);
v_a_1051_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1046_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1046_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v___x_1003_);
v_a_1059_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1041_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1041_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
v___jp_1067_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = l_Subarray_copy___redArg(v___y_1071_);
v___x_1076_ = l_Lean_mkAppN(v_f_1017_, v___x_1075_);
lean_dec_ref(v___x_1075_);
lean_inc_ref(v___x_1076_);
v___x_1077_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1007_, v___x_1076_, v___y_1072_, v___y_1070_, v___y_1073_, v___y_1068_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_8045__overap_1079_; lean_object* v___x_1080_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref(v___x_1077_);
lean_inc(v___x_1010_);
lean_inc(v___x_1009_);
lean_inc_ref(v___x_1008_);
lean_inc_ref(v___x_1003_);
v___x_8045__overap_1079_ = l_Lean_isTracingEnabledFor___redArg(v___x_1003_, v___x_1008_, v___x_1009_, v___x_1010_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1073_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1072_);
v___x_1080_ = lean_apply_5(v___x_8045__overap_1079_, v___y_1072_, v___y_1070_, v___y_1073_, v___y_1068_, lean_box(0));
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_lower_1082_; lean_object* v_upper_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1115_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v___x_1080_);
v_lower_1082_ = lean_ctor_get(v___y_1074_, 0);
v_upper_1083_ = lean_ctor_get(v___y_1074_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___y_1074_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1085_ = v___y_1074_;
v_isShared_1086_ = v_isSharedCheck_1115_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_upper_1083_);
lean_inc(v_lower_1082_);
lean_dec(v___y_1074_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1115_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1087_ = l_Array_toSubarray___redArg(v_args_1018_, v_lower_1082_, v_upper_1083_);
lean_inc(v___f_1014_);
lean_inc(v___x_1013_);
lean_inc(v___x_1010_);
lean_inc_ref(v___x_1008_);
lean_inc(v_a_1078_);
lean_inc_ref(v_positions_1002_);
lean_inc_ref(v___x_1003_);
v___f_1088_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed), 18, 12);
lean_closure_set(v___f_1088_, 0, v___x_1003_);
lean_closure_set(v___f_1088_, 1, v___x_1011_);
lean_closure_set(v___f_1088_, 2, v_positions_1002_);
lean_closure_set(v___f_1088_, 3, v_a_1078_);
lean_closure_set(v___f_1088_, 4, v___x_1008_);
lean_closure_set(v___f_1088_, 5, v___x_1009_);
lean_closure_set(v___f_1088_, 6, v___x_1010_);
lean_closure_set(v___f_1088_, 7, v___x_1076_);
lean_closure_set(v___f_1088_, 8, v___x_1087_);
lean_closure_set(v___f_1088_, 9, v_k_1012_);
lean_closure_set(v___f_1088_, 10, v___x_1013_);
lean_closure_set(v___f_1088_, 11, v___f_1014_);
v___x_1089_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1002_);
v___x_1090_ = lean_unbox(v_a_1081_);
lean_dec(v_a_1081_);
if (v___x_1090_ == 0)
{
lean_del_object(v___x_1085_);
lean_dec(v___f_1014_);
lean_dec(v___x_1013_);
lean_dec(v___x_1010_);
lean_dec_ref(v___x_1008_);
v___y_1025_ = v___y_1069_;
v___y_1026_ = v___f_1088_;
v___y_1027_ = v_a_1078_;
v___y_1028_ = v___x_1089_;
v___y_1029_ = v___y_1072_;
v___y_1030_ = v___y_1070_;
v___y_1031_ = v___y_1073_;
v___y_1032_ = v___y_1068_;
goto v___jp_1024_;
}
else
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_toMonadRef_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___f_1091_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2));
v___x_1093_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1094_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1092_, v___x_1013_, v___x_1093_);
v___x_1095_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1091_, v___f_1014_, v___x_1094_);
v_toMonadRef_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_toMonadRef_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1098_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3);
lean_inc(v___x_1089_);
v___x_1099_ = l_Nat_reprFast(v___x_1089_);
v___x_1100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
v___x_1101_ = l_Lean_MessageData_ofFormat(v___x_1100_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 7);
lean_ctor_set(v___x_1085_, 1, v___x_1101_);
lean_ctor_set(v___x_1085_, 0, v___x_1098_);
v___x_1103_ = v___x_1085_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_8063__overap_1104_; lean_object* v___x_1105_; 
lean_inc_ref(v___x_1003_);
v___x_8063__overap_1104_ = l_Lean_addTrace___redArg(v___x_1003_, v___x_1008_, v_toMonadRef_1096_, v___x_1097_, v___x_1010_, v___x_1103_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1073_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1072_);
v___x_1105_ = lean_apply_5(v___x_8063__overap_1104_, v___y_1072_, v___y_1070_, v___y_1073_, v___y_1068_, lean_box(0));
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_dec_ref(v___x_1105_);
v___y_1025_ = v___y_1069_;
v___y_1026_ = v___f_1088_;
v___y_1027_ = v_a_1078_;
v___y_1028_ = v___x_1089_;
v___y_1029_ = v___y_1072_;
v___y_1030_ = v___y_1070_;
v___y_1031_ = v___y_1073_;
v___y_1032_ = v___y_1068_;
goto v___jp_1024_;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v___x_1089_);
lean_dec_ref(v___f_1088_);
lean_dec(v_a_1078_);
lean_dec(v___y_1069_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v___f_1004_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v_positions_1002_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_a_1078_);
lean_dec_ref(v___x_1076_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1069_);
lean_dec_ref(v_args_1018_);
lean_dec(v___f_1014_);
lean_dec(v___x_1013_);
lean_dec_ref(v_k_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v___x_1010_);
lean_dec(v___x_1009_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v___f_1004_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v_positions_1002_);
v_a_1116_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1080_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1080_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v___x_1076_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1069_);
lean_dec_ref(v_args_1018_);
lean_dec(v___f_1014_);
lean_dec(v___x_1013_);
lean_dec_ref(v_k_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v___x_1010_);
lean_dec(v___x_1009_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v___f_1004_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v_positions_1002_);
v_a_1124_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1077_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1077_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
v___jp_1132_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1137_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1015_);
lean_inc_ref(v_args_1018_);
v___x_1138_ = l_Array_toSubarray___redArg(v_args_1018_, v___x_1137_, v_numIndParams_1015_);
v___x_1139_ = lean_nat_add(v_numIndParams_1015_, v_numTypeFormers_1007_);
lean_dec(v_numIndParams_1015_);
v___x_1140_ = lean_array_get_size(v_args_1018_);
v___x_1141_ = lean_nat_dec_le(v___x_1139_, v___x_1137_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1139_);
lean_ctor_set(v___x_1142_, 1, v___x_1140_);
v___y_1068_ = v___y_1136_;
v___y_1069_ = v___x_1137_;
v___y_1070_ = v___y_1134_;
v___y_1071_ = v___x_1138_;
v___y_1072_ = v___y_1133_;
v___y_1073_ = v___y_1135_;
v___y_1074_ = v___x_1142_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1143_; 
lean_dec(v___x_1139_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1137_);
lean_ctor_set(v___x_1143_, 1, v___x_1140_);
v___y_1068_ = v___y_1136_;
v___y_1069_ = v___x_1137_;
v___y_1070_ = v___y_1134_;
v___y_1071_ = v___x_1138_;
v___y_1072_ = v___y_1133_;
v___y_1073_ = v___y_1135_;
v___y_1074_ = v___x_1143_;
goto v___jp_1067_;
}
}
v___jp_1144_:
{
lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v___x_1149_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_positions_1193_ = _args[0];
lean_object* v___x_1194_ = _args[1];
lean_object* v___f_1195_ = _args[2];
lean_object* v___f_1196_ = _args[3];
lean_object* v___x_1197_ = _args[4];
lean_object* v_numTypeFormers_1198_ = _args[5];
lean_object* v___x_1199_ = _args[6];
lean_object* v___x_1200_ = _args[7];
lean_object* v___x_1201_ = _args[8];
lean_object* v___x_1202_ = _args[9];
lean_object* v_k_1203_ = _args[10];
lean_object* v___x_1204_ = _args[11];
lean_object* v___f_1205_ = _args[12];
lean_object* v_numIndParams_1206_ = _args[13];
lean_object* v_a_1207_ = _args[14];
lean_object* v_f_1208_ = _args[15];
lean_object* v_args_1209_ = _args[16];
lean_object* v___y_1210_ = _args[17];
lean_object* v___y_1211_ = _args[18];
lean_object* v___y_1212_ = _args[19];
lean_object* v___y_1213_ = _args[20];
lean_object* v___y_1214_ = _args[21];
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v_positions_1193_, v___x_1194_, v___f_1195_, v___f_1196_, v___x_1197_, v_numTypeFormers_1198_, v___x_1199_, v___x_1200_, v___x_1201_, v___x_1202_, v_k_1203_, v___x_1204_, v___f_1205_, v_numIndParams_1206_, v_a_1207_, v_f_1208_, v_args_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1215_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_instMonadEIO(lean_box(0));
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1218_ = l_StateRefT_x27_instMonad___redArg(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1226_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1227_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1226_, v___x_1225_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1229_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1230_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1229_, v___x_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1237_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1238_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__2));
v___x_1240_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1239_, v___x_1238_, v___x_1237_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v___x_1244_; 
v___x_1241_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14);
v___f_1242_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1243_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__1));
v___x_1244_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1243_, v___f_1242_, v___x_1241_);
return v___x_1244_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16));
v___x_1247_ = l_Lean_stringToMessageData(v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1248_, lean_object* v_numIndParams_1249_, lean_object* v_positions_1250_, lean_object* v_k_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_toApplicative_1258_; lean_object* v_toFunctor_1259_; lean_object* v_toSeq_1260_; lean_object* v_toSeqLeft_1261_; lean_object* v_toSeqRight_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1440_; 
v___x_1257_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_toApplicative_1258_);
v_toFunctor_1259_ = lean_ctor_get(v_toApplicative_1258_, 0);
v_toSeq_1260_ = lean_ctor_get(v_toApplicative_1258_, 2);
v_toSeqLeft_1261_ = lean_ctor_get(v_toApplicative_1258_, 3);
v_toSeqRight_1262_ = lean_ctor_get(v_toApplicative_1258_, 4);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_toApplicative_1258_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_toApplicative_1258_, 1);
lean_dec(v_unused_1441_);
v___x_1264_ = v_toApplicative_1258_;
v_isShared_1265_ = v_isSharedCheck_1440_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_toSeqRight_1262_);
lean_inc(v_toSeqLeft_1261_);
lean_inc(v_toSeq_1260_);
lean_inc(v_toFunctor_1259_);
lean_dec(v_toApplicative_1258_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1440_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___x_1275_; 
v___f_1266_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1267_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref(v_toFunctor_1259_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toFunctor_1259_);
v___f_1269_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1269_, 0, v_toFunctor_1259_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___f_1268_);
lean_ctor_set(v___x_1270_, 1, v___f_1269_);
v___f_1271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1271_, 0, v_toSeqRight_1262_);
v___f_1272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1272_, 0, v_toSeqLeft_1261_);
v___f_1273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1273_, 0, v_toSeq_1260_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 4, v___f_1271_);
lean_ctor_set(v___x_1264_, 3, v___f_1272_);
lean_ctor_set(v___x_1264_, 2, v___f_1273_);
lean_ctor_set(v___x_1264_, 1, v___f_1266_);
lean_ctor_set(v___x_1264_, 0, v___x_1270_);
v___x_1275_ = v___x_1264_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v___f_1266_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v___f_1273_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v___f_1272_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v___f_1271_);
v___x_1275_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_toApplicative_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1437_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v___f_1267_);
v___x_1277_ = l_StateRefT_x27_instMonad___redArg(v___x_1276_);
v_toApplicative_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v___x_1277_, 1);
lean_dec(v_unused_1438_);
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1437_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_toApplicative_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1437_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_toFunctor_1282_; lean_object* v_toSeq_1283_; lean_object* v_toSeqLeft_1284_; lean_object* v_toSeqRight_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1435_; 
v_toFunctor_1282_ = lean_ctor_get(v_toApplicative_1278_, 0);
v_toSeq_1283_ = lean_ctor_get(v_toApplicative_1278_, 2);
v_toSeqLeft_1284_ = lean_ctor_get(v_toApplicative_1278_, 3);
v_toSeqRight_1285_ = lean_ctor_get(v_toApplicative_1278_, 4);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_toApplicative_1278_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_toApplicative_1278_, 1);
lean_dec(v_unused_1436_);
v___x_1287_ = v_toApplicative_1278_;
v_isShared_1288_ = v_isSharedCheck_1435_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_toSeqRight_1285_);
lean_inc(v_toSeqLeft_1284_);
lean_inc(v_toSeq_1283_);
lean_inc(v_toFunctor_1282_);
lean_dec(v_toApplicative_1278_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1435_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___f_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; lean_object* v___x_1293_; lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___x_1298_; 
v___f_1289_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1290_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1282_);
v___f_1291_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1291_, 0, v_toFunctor_1282_);
v___f_1292_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1292_, 0, v_toFunctor_1282_);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___f_1291_);
lean_ctor_set(v___x_1293_, 1, v___f_1292_);
v___f_1294_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1294_, 0, v_toSeqRight_1285_);
v___f_1295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1295_, 0, v_toSeqLeft_1284_);
v___f_1296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1296_, 0, v_toSeq_1283_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v___f_1294_);
lean_ctor_set(v___x_1287_, 3, v___f_1295_);
lean_ctor_set(v___x_1287_, 2, v___f_1296_);
lean_ctor_set(v___x_1287_, 1, v___f_1289_);
lean_ctor_set(v___x_1287_, 0, v___x_1293_);
v___x_1298_ = v___x_1287_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___f_1289_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v___f_1296_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v___f_1295_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v___f_1294_);
v___x_1298_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___f_1290_);
lean_ctor_set(v___x_1280_, 0, v___x_1298_);
v___x_1300_ = v___x_1280_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___f_1290_);
v___x_1300_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___f_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v_toApplicative_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1431_; 
v___f_1301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1303_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1304_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1257_, 1);
lean_dec(v_unused_1432_);
v___x_1306_ = v___x_1257_;
v_isShared_1307_ = v_isSharedCheck_1431_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_toApplicative_1304_);
lean_dec(v___x_1257_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1431_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v_toFunctor_1308_; lean_object* v_toSeq_1309_; lean_object* v_toSeqLeft_1310_; lean_object* v_toSeqRight_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1429_; 
v_toFunctor_1308_ = lean_ctor_get(v_toApplicative_1304_, 0);
v_toSeq_1309_ = lean_ctor_get(v_toApplicative_1304_, 2);
v_toSeqLeft_1310_ = lean_ctor_get(v_toApplicative_1304_, 3);
v_toSeqRight_1311_ = lean_ctor_get(v_toApplicative_1304_, 4);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_toApplicative_1304_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v_toApplicative_1304_, 1);
lean_dec(v_unused_1430_);
v___x_1313_ = v_toApplicative_1304_;
v_isShared_1314_ = v_isSharedCheck_1429_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_toSeqRight_1311_);
lean_inc(v_toSeqLeft_1310_);
lean_inc(v_toSeq_1309_);
lean_inc(v_toFunctor_1308_);
lean_dec(v_toApplicative_1304_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1429_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___x_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___x_1322_; 
lean_inc_ref(v_toFunctor_1308_);
v___f_1315_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1315_, 0, v_toFunctor_1308_);
v___f_1316_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1316_, 0, v_toFunctor_1308_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___f_1315_);
lean_ctor_set(v___x_1317_, 1, v___f_1316_);
v___f_1318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1318_, 0, v_toSeqRight_1311_);
v___f_1319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1319_, 0, v_toSeqLeft_1310_);
v___f_1320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1320_, 0, v_toSeq_1309_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 4, v___f_1318_);
lean_ctor_set(v___x_1313_, 3, v___f_1319_);
lean_ctor_set(v___x_1313_, 2, v___f_1320_);
lean_ctor_set(v___x_1313_, 1, v___f_1266_);
lean_ctor_set(v___x_1313_, 0, v___x_1317_);
v___x_1322_ = v___x_1313_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___f_1266_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v___f_1320_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v___f_1319_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v___f_1318_);
v___x_1322_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___f_1267_);
lean_ctor_set(v___x_1306_, 0, v___x_1322_);
v___x_1324_ = v___x_1306_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___f_1267_);
v___x_1324_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = l_StateRefT_x27_instMonad___redArg(v___x_1324_);
v___x_1326_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1326_, 0, lean_box(0));
lean_closure_set(v___x_1326_, 1, lean_box(0));
lean_closure_set(v___x_1326_, 2, v___x_1325_);
v___x_1327_ = l_instMonadControlTOfPure___redArg(v___x_1326_);
lean_inc(v_a_1255_);
lean_inc_ref(v_a_1254_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
lean_inc_ref(v_below_1248_);
v___x_1328_ = lean_infer_type(v_below_1248_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_7064__overap_1332_; lean_object* v___x_1333_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1328_);
v___x_1330_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12));
v___x_1331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
lean_inc_ref(v___x_1300_);
v___x_7064__overap_1332_ = l_Lean_isTracingEnabledFor___redArg(v___x_1300_, v___x_1303_, v___x_1330_, v___x_1331_);
lean_inc(v_a_1255_);
lean_inc_ref(v_a_1254_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
v___x_1333_ = lean_apply_5(v___x_7064__overap_1332_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, lean_box(0));
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___f_1335_; lean_object* v___f_1336_; lean_object* v___x_1337_; lean_object* v_numTypeFormers_1338_; lean_object* v___f_1339_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; uint8_t v___x_1394_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref(v___x_1333_);
v___f_1335_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13));
lean_inc_ref(v___x_1300_);
v___f_1336_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_1336_, 0, v___x_1300_);
v___x_1337_ = l_Lean_instInhabitedExpr;
v_numTypeFormers_1338_ = lean_array_get_size(v_positions_1250_);
lean_inc(v_a_1329_);
lean_inc_ref(v___x_1300_);
v___f_1339_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 22, 15);
lean_closure_set(v___f_1339_, 0, v_positions_1250_);
lean_closure_set(v___f_1339_, 1, v___x_1300_);
lean_closure_set(v___f_1339_, 2, v___f_1336_);
lean_closure_set(v___f_1339_, 3, v___f_1335_);
lean_closure_set(v___f_1339_, 4, v___x_1327_);
lean_closure_set(v___f_1339_, 5, v_numTypeFormers_1338_);
lean_closure_set(v___f_1339_, 6, v___x_1303_);
lean_closure_set(v___f_1339_, 7, v___x_1330_);
lean_closure_set(v___f_1339_, 8, v___x_1331_);
lean_closure_set(v___f_1339_, 9, v___x_1337_);
lean_closure_set(v___f_1339_, 10, v_k_1251_);
lean_closure_set(v___f_1339_, 11, v___x_1302_);
lean_closure_set(v___f_1339_, 12, v___f_1301_);
lean_closure_set(v___f_1339_, 13, v_numIndParams_1249_);
lean_closure_set(v___f_1339_, 14, v_a_1329_);
v___x_1394_ = lean_unbox(v_a_1334_);
lean_dec(v_a_1334_);
if (v___x_1394_ == 0)
{
v___y_1353_ = v_a_1252_;
v___y_1354_ = v_a_1253_;
v___y_1355_ = v_a_1254_;
v___y_1356_ = v_a_1255_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1395_; lean_object* v_toMonadRef_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_7719__overap_1401_; lean_object* v___x_1402_; 
v___x_1395_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15);
v_toMonadRef_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc_ref(v_toMonadRef_1396_);
v___x_1397_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1398_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17);
lean_inc(v_a_1329_);
v___x_1399_ = l_Lean_MessageData_ofExpr(v_a_1329_);
v___x_1400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
lean_inc_ref(v___x_1300_);
v___x_7719__overap_1401_ = l_Lean_addTrace___redArg(v___x_1300_, v___x_1303_, v_toMonadRef_1396_, v___x_1397_, v___x_1331_, v___x_1400_);
lean_inc(v_a_1255_);
lean_inc_ref(v_a_1254_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
v___x_1402_ = lean_apply_5(v___x_7719__overap_1401_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, lean_box(0));
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_dec_ref(v___x_1402_);
v___y_1353_ = v_a_1252_;
v___y_1354_ = v_a_1253_;
v___y_1355_ = v_a_1254_;
v___y_1356_ = v_a_1255_;
goto v___jp_1352_;
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec_ref(v___f_1339_);
lean_dec(v_a_1329_);
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_below_1248_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
v___jp_1340_:
{
lean_object* v_dummy_1345_; lean_object* v_nargs_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_7438__overap_1350_; lean_object* v___x_1351_; 
v_dummy_1345_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
v_nargs_1346_ = l_Lean_Expr_getAppNumArgs(v_a_1329_);
lean_inc(v_nargs_1346_);
v___x_1347_ = lean_mk_array(v_nargs_1346_, v_dummy_1345_);
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_sub(v_nargs_1346_, v___x_1348_);
lean_dec(v_nargs_1346_);
v___x_7438__overap_1350_ = l_Lean_Expr_withAppAux___redArg(v___f_1339_, v_a_1329_, v___x_1347_, v___x_1349_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
v___x_1351_ = lean_apply_5(v___x_7438__overap_1350_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, lean_box(0));
return v___x_1351_;
}
v___jp_1352_:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Meta_isTypeCorrect(v_below_1248_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; uint8_t v___x_1359_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref(v___x_1357_);
v___x_1359_ = lean_unbox(v_a_1358_);
lean_dec(v_a_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_7660__overap_1360_; lean_object* v___x_1361_; 
lean_inc_ref(v___x_1300_);
v___x_7660__overap_1360_ = l_Lean_isTracingEnabledFor___redArg(v___x_1300_, v___x_1303_, v___x_1330_, v___x_1331_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
v___x_1361_ = lean_apply_5(v___x_7660__overap_1360_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, lean_box(0));
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; uint8_t v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = lean_unbox(v_a_1362_);
lean_dec(v_a_1362_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v___x_1300_);
v___y_1341_ = v___y_1353_;
v___y_1342_ = v___y_1354_;
v___y_1343_ = v___y_1355_;
v___y_1344_ = v___y_1356_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1364_; lean_object* v_toMonadRef_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_7697__overap_1368_; lean_object* v___x_1369_; 
v___x_1364_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15);
v_toMonadRef_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc_ref(v_toMonadRef_1365_);
v___x_1366_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1367_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__4);
v___x_7697__overap_1368_ = l_Lean_addTrace___redArg(v___x_1300_, v___x_1303_, v_toMonadRef_1365_, v___x_1366_, v___x_1331_, v___x_1367_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
v___x_1369_ = lean_apply_5(v___x_7697__overap_1368_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, lean_box(0));
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec_ref(v___x_1369_);
v___y_1341_ = v___y_1353_;
v___y_1342_ = v___y_1354_;
v___y_1343_ = v___y_1355_;
v___y_1344_ = v___y_1356_;
goto v___jp_1340_;
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v___f_1339_);
lean_dec(v_a_1329_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v___f_1339_);
lean_dec(v_a_1329_);
lean_dec_ref(v___x_1300_);
v_a_1378_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1361_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1361_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_dec_ref(v___x_1300_);
v___y_1341_ = v___y_1353_;
v___y_1342_ = v___y_1354_;
v___y_1343_ = v___y_1355_;
v___y_1344_ = v___y_1356_;
goto v___jp_1340_;
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v___f_1339_);
lean_dec(v_a_1329_);
lean_dec_ref(v___x_1300_);
v_a_1386_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1357_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1357_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_a_1329_);
lean_dec_ref(v___x_1327_);
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_k_1251_);
lean_dec_ref(v_positions_1250_);
lean_dec(v_numIndParams_1249_);
lean_dec_ref(v_below_1248_);
v_a_1411_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1333_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1333_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v___x_1327_);
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_k_1251_);
lean_dec_ref(v_positions_1250_);
lean_dec(v_numIndParams_1249_);
lean_dec_ref(v_below_1248_);
v_a_1419_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1328_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1328_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1442_, lean_object* v_numIndParams_1443_, lean_object* v_positions_1444_, lean_object* v_k_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1442_, v_numIndParams_1443_, v_positions_1444_, v_k_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1452_, lean_object* v_inst_1453_, lean_object* v_below_1454_, lean_object* v_numIndParams_1455_, lean_object* v_positions_1456_, lean_object* v_k_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1454_, v_numIndParams_1455_, v_positions_1456_, v_k_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_inst_1465_, lean_object* v_below_1466_, lean_object* v_numIndParams_1467_, lean_object* v_positions_1468_, lean_object* v_k_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1464_, v_inst_1465_, v_below_1466_, v_numIndParams_1467_, v_positions_1468_, v_k_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_inst_1465_);
return v_res_1475_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = lean_unsigned_to_nat(32u);
v___x_1477_ = lean_mk_empty_array_with_capacity(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1479_ = ((size_t)5ULL);
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_unsigned_to_nat(32u);
v___x_1482_ = lean_mk_empty_array_with_capacity(v___x_1481_);
v___x_1483_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1484_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
lean_ctor_set(v___x_1484_, 2, v___x_1480_);
lean_ctor_set(v___x_1484_, 3, v___x_1480_);
lean_ctor_set_usize(v___x_1484_, 4, v___x_1479_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; lean_object* v_traceState_1488_; lean_object* v_traces_1489_; lean_object* v___x_1490_; lean_object* v_traceState_1491_; lean_object* v_env_1492_; lean_object* v_nextMacroScope_1493_; lean_object* v_ngen_1494_; lean_object* v_auxDeclNGen_1495_; lean_object* v_cache_1496_; lean_object* v_messages_1497_; lean_object* v_infoState_1498_; lean_object* v_snapshotTasks_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1518_; 
v___x_1487_ = lean_st_ref_get(v___y_1485_);
v_traceState_1488_ = lean_ctor_get(v___x_1487_, 4);
lean_inc_ref(v_traceState_1488_);
lean_dec(v___x_1487_);
v_traces_1489_ = lean_ctor_get(v_traceState_1488_, 0);
lean_inc_ref(v_traces_1489_);
lean_dec_ref(v_traceState_1488_);
v___x_1490_ = lean_st_ref_take(v___y_1485_);
v_traceState_1491_ = lean_ctor_get(v___x_1490_, 4);
v_env_1492_ = lean_ctor_get(v___x_1490_, 0);
v_nextMacroScope_1493_ = lean_ctor_get(v___x_1490_, 1);
v_ngen_1494_ = lean_ctor_get(v___x_1490_, 2);
v_auxDeclNGen_1495_ = lean_ctor_get(v___x_1490_, 3);
v_cache_1496_ = lean_ctor_get(v___x_1490_, 5);
v_messages_1497_ = lean_ctor_get(v___x_1490_, 6);
v_infoState_1498_ = lean_ctor_get(v___x_1490_, 7);
v_snapshotTasks_1499_ = lean_ctor_get(v___x_1490_, 8);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1501_ = v___x_1490_;
v_isShared_1502_ = v_isSharedCheck_1518_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_snapshotTasks_1499_);
lean_inc(v_infoState_1498_);
lean_inc(v_messages_1497_);
lean_inc(v_cache_1496_);
lean_inc(v_traceState_1491_);
lean_inc(v_auxDeclNGen_1495_);
lean_inc(v_ngen_1494_);
lean_inc(v_nextMacroScope_1493_);
lean_inc(v_env_1492_);
lean_dec(v___x_1490_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1518_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
uint64_t v_tid_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1516_; 
v_tid_1503_ = lean_ctor_get_uint64(v_traceState_1491_, sizeof(void*)*1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_traceState_1491_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_traceState_1491_, 0);
lean_dec(v_unused_1517_);
v___x_1505_ = v_traceState_1491_;
v_isShared_1506_ = v_isSharedCheck_1516_;
goto v_resetjp_1504_;
}
else
{
lean_dec(v_traceState_1491_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1516_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1507_);
v___x_1509_ = v___x_1505_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1507_);
lean_ctor_set_uint64(v_reuseFailAlloc_1515_, sizeof(void*)*1, v_tid_1503_);
v___x_1509_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 4, v___x_1509_);
v___x_1511_ = v___x_1501_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_env_1492_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_nextMacroScope_1493_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_ngen_1494_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_auxDeclNGen_1495_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1514_, 5, v_cache_1496_);
lean_ctor_set(v_reuseFailAlloc_1514_, 6, v_messages_1497_);
lean_ctor_set(v_reuseFailAlloc_1514_, 7, v_infoState_1498_);
lean_ctor_set(v_reuseFailAlloc_1514_, 8, v_snapshotTasks_1499_);
v___x_1511_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_st_ref_set(v___y_1485_, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_traces_1489_);
return v___x_1513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1519_);
lean_dec(v___y_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1525_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1534_, lean_object* v_opt_1535_){
_start:
{
lean_object* v_name_1536_; lean_object* v_defValue_1537_; lean_object* v_map_1538_; lean_object* v___x_1539_; 
v_name_1536_ = lean_ctor_get(v_opt_1535_, 0);
v_defValue_1537_ = lean_ctor_get(v_opt_1535_, 1);
v_map_1538_ = lean_ctor_get(v_opts_1534_, 0);
v___x_1539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1538_, v_name_1536_);
if (lean_obj_tag(v___x_1539_) == 0)
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_unbox(v_defValue_1537_);
return v___x_1540_;
}
else
{
lean_object* v_val_1541_; 
v_val_1541_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_val_1541_);
lean_dec_ref(v___x_1539_);
if (lean_obj_tag(v_val_1541_) == 1)
{
uint8_t v_v_1542_; 
v_v_1542_ = lean_ctor_get_uint8(v_val_1541_, 0);
lean_dec_ref(v_val_1541_);
return v_v_1542_;
}
else
{
uint8_t v___x_1543_; 
lean_dec(v_val_1541_);
v___x_1543_ = lean_unbox(v_defValue_1537_);
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1544_, lean_object* v_opt_1545_){
_start:
{
uint8_t v_res_1546_; lean_object* v_r_1547_; 
v_res_1546_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1544_, v_opt_1545_);
lean_dec_ref(v_opt_1545_);
lean_dec_ref(v_opts_1544_);
v_r_1547_ = lean_box(v_res_1546_);
return v_r_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1548_, lean_object* v_fnIndex_1549_, lean_object* v_recArg_1550_, lean_object* v_below_1551_, lean_object* v_Cs_1552_, lean_object* v_belowDict_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_array_get_borrowed(v___x_1548_, v_Cs_1552_, v_fnIndex_1549_);
lean_inc(v___x_1559_);
v___x_1560_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1559_, v_belowDict_1553_, v_recArg_1550_, v_below_1551_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1561_, lean_object* v_fnIndex_1562_, lean_object* v_recArg_1563_, lean_object* v_below_1564_, lean_object* v_Cs_1565_, lean_object* v_belowDict_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1561_, v_fnIndex_1562_, v_recArg_1563_, v_below_1564_, v_Cs_1565_, v_belowDict_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_Cs_1565_);
lean_dec(v_fnIndex_1562_);
return v_res_1572_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1575_ = l_Lean_stringToMessageData(v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1579_, lean_object* v_recArg_1580_, lean_object* v_x_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
lean_inc(v___y_1585_);
lean_inc_ref(v___y_1584_);
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
v___x_1587_ = lean_infer_type(v_below_1579_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1602_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1602_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1602_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1592_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1593_ = l_Lean_MessageData_ofExpr(v_recArg_1580_);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = l_Lean_MessageData_ofExpr(v_a_1588_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1598_);
v___x_1600_ = v___x_1590_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_recArg_1580_);
v_a_1603_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1587_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1587_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1611_, lean_object* v_recArg_1612_, lean_object* v_x_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1611_, v_recArg_1612_, v_x_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v_x_1613_);
return v_res_1619_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_e_1620_){
_start:
{
if (lean_obj_tag(v_e_1620_) == 0)
{
uint8_t v___x_1621_; 
v___x_1621_ = 2;
return v___x_1621_;
}
else
{
uint8_t v___x_1622_; 
v___x_1622_ = 0;
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_e_1623_){
_start:
{
uint8_t v_res_1624_; lean_object* v_r_1625_; 
v_res_1624_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_e_1623_);
lean_dec_ref(v_e_1623_);
v_r_1625_ = lean_box(v_res_1624_);
return v_r_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1626_, lean_object* v_opt_1627_){
_start:
{
lean_object* v_name_1628_; lean_object* v_defValue_1629_; lean_object* v_map_1630_; lean_object* v___x_1631_; 
v_name_1628_ = lean_ctor_get(v_opt_1627_, 0);
v_defValue_1629_ = lean_ctor_get(v_opt_1627_, 1);
v_map_1630_ = lean_ctor_get(v_opts_1626_, 0);
v___x_1631_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1630_, v_name_1628_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_inc(v_defValue_1629_);
return v_defValue_1629_;
}
else
{
lean_object* v_val_1632_; 
v_val_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_val_1632_);
lean_dec_ref(v___x_1631_);
if (lean_obj_tag(v_val_1632_) == 3)
{
lean_object* v_v_1633_; 
v_v_1633_ = lean_ctor_get(v_val_1632_, 0);
lean_inc(v_v_1633_);
lean_dec_ref(v_val_1632_);
return v_v_1633_;
}
else
{
lean_dec(v_val_1632_);
lean_inc(v_defValue_1629_);
return v_defValue_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1634_, lean_object* v_opt_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1634_, v_opt_1635_);
lean_dec_ref(v_opt_1635_);
lean_dec_ref(v_opts_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(lean_object* v_x_1637_){
_start:
{
if (lean_obj_tag(v_x_1637_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_a_1639_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v_x_1637_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v_x_1637_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 1);
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_a_1647_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v_x_1637_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v_x_1637_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 0);
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg___boxed(lean_object* v_x_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_x_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(size_t v_sz_1658_, size_t v_i_1659_, lean_object* v_bs_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_usize_dec_lt(v_i_1659_, v_sz_1658_);
if (v___x_1661_ == 0)
{
return v_bs_1660_;
}
else
{
lean_object* v_v_1662_; lean_object* v_msg_1663_; lean_object* v___x_1664_; lean_object* v_bs_x27_1665_; size_t v___x_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v_v_1662_ = lean_array_uget_borrowed(v_bs_1660_, v_i_1659_);
v_msg_1663_ = lean_ctor_get(v_v_1662_, 1);
lean_inc_ref(v_msg_1663_);
v___x_1664_ = lean_unsigned_to_nat(0u);
v_bs_x27_1665_ = lean_array_uset(v_bs_1660_, v_i_1659_, v___x_1664_);
v___x_1666_ = ((size_t)1ULL);
v___x_1667_ = lean_usize_add(v_i_1659_, v___x_1666_);
v___x_1668_ = lean_array_uset(v_bs_x27_1665_, v_i_1659_, v_msg_1663_);
v_i_1659_ = v___x_1667_;
v_bs_1660_ = v___x_1668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_1670_, lean_object* v_i_1671_, lean_object* v_bs_1672_){
_start:
{
size_t v_sz_boxed_1673_; size_t v_i_boxed_1674_; lean_object* v_res_1675_; 
v_sz_boxed_1673_ = lean_unbox_usize(v_sz_1670_);
lean_dec(v_sz_1670_);
v_i_boxed_1674_ = lean_unbox_usize(v_i_1671_);
lean_dec(v_i_1671_);
v_res_1675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(v_sz_boxed_1673_, v_i_boxed_1674_, v_bs_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_oldTraces_1676_, lean_object* v_data_1677_, lean_object* v_ref_1678_, lean_object* v_msg_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_fileName_1685_; lean_object* v_fileMap_1686_; lean_object* v_options_1687_; lean_object* v_currRecDepth_1688_; lean_object* v_maxRecDepth_1689_; lean_object* v_ref_1690_; lean_object* v_currNamespace_1691_; lean_object* v_openDecls_1692_; lean_object* v_initHeartbeats_1693_; lean_object* v_maxHeartbeats_1694_; lean_object* v_quotContext_1695_; lean_object* v_currMacroScope_1696_; uint8_t v_diag_1697_; lean_object* v_cancelTk_x3f_1698_; uint8_t v_suppressElabErrors_1699_; lean_object* v_inheritedTraceOptions_1700_; lean_object* v___x_1701_; lean_object* v_traceState_1702_; lean_object* v_traces_1703_; lean_object* v_ref_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; size_t v_sz_1707_; size_t v___x_1708_; lean_object* v___x_1709_; lean_object* v_msg_1710_; lean_object* v___x_1711_; lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1749_; 
v_fileName_1685_ = lean_ctor_get(v___y_1682_, 0);
v_fileMap_1686_ = lean_ctor_get(v___y_1682_, 1);
v_options_1687_ = lean_ctor_get(v___y_1682_, 2);
v_currRecDepth_1688_ = lean_ctor_get(v___y_1682_, 3);
v_maxRecDepth_1689_ = lean_ctor_get(v___y_1682_, 4);
v_ref_1690_ = lean_ctor_get(v___y_1682_, 5);
v_currNamespace_1691_ = lean_ctor_get(v___y_1682_, 6);
v_openDecls_1692_ = lean_ctor_get(v___y_1682_, 7);
v_initHeartbeats_1693_ = lean_ctor_get(v___y_1682_, 8);
v_maxHeartbeats_1694_ = lean_ctor_get(v___y_1682_, 9);
v_quotContext_1695_ = lean_ctor_get(v___y_1682_, 10);
v_currMacroScope_1696_ = lean_ctor_get(v___y_1682_, 11);
v_diag_1697_ = lean_ctor_get_uint8(v___y_1682_, sizeof(void*)*14);
v_cancelTk_x3f_1698_ = lean_ctor_get(v___y_1682_, 12);
v_suppressElabErrors_1699_ = lean_ctor_get_uint8(v___y_1682_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1700_ = lean_ctor_get(v___y_1682_, 13);
v___x_1701_ = lean_st_ref_get(v___y_1683_);
v_traceState_1702_ = lean_ctor_get(v___x_1701_, 4);
lean_inc_ref(v_traceState_1702_);
lean_dec(v___x_1701_);
v_traces_1703_ = lean_ctor_get(v_traceState_1702_, 0);
lean_inc_ref(v_traces_1703_);
lean_dec_ref(v_traceState_1702_);
v_ref_1704_ = l_Lean_replaceRef(v_ref_1678_, v_ref_1690_);
lean_inc_ref(v_inheritedTraceOptions_1700_);
lean_inc(v_cancelTk_x3f_1698_);
lean_inc(v_currMacroScope_1696_);
lean_inc(v_quotContext_1695_);
lean_inc(v_maxHeartbeats_1694_);
lean_inc(v_initHeartbeats_1693_);
lean_inc(v_openDecls_1692_);
lean_inc(v_currNamespace_1691_);
lean_inc(v_maxRecDepth_1689_);
lean_inc(v_currRecDepth_1688_);
lean_inc_ref(v_options_1687_);
lean_inc_ref(v_fileMap_1686_);
lean_inc_ref(v_fileName_1685_);
v___x_1705_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1705_, 0, v_fileName_1685_);
lean_ctor_set(v___x_1705_, 1, v_fileMap_1686_);
lean_ctor_set(v___x_1705_, 2, v_options_1687_);
lean_ctor_set(v___x_1705_, 3, v_currRecDepth_1688_);
lean_ctor_set(v___x_1705_, 4, v_maxRecDepth_1689_);
lean_ctor_set(v___x_1705_, 5, v_ref_1704_);
lean_ctor_set(v___x_1705_, 6, v_currNamespace_1691_);
lean_ctor_set(v___x_1705_, 7, v_openDecls_1692_);
lean_ctor_set(v___x_1705_, 8, v_initHeartbeats_1693_);
lean_ctor_set(v___x_1705_, 9, v_maxHeartbeats_1694_);
lean_ctor_set(v___x_1705_, 10, v_quotContext_1695_);
lean_ctor_set(v___x_1705_, 11, v_currMacroScope_1696_);
lean_ctor_set(v___x_1705_, 12, v_cancelTk_x3f_1698_);
lean_ctor_set(v___x_1705_, 13, v_inheritedTraceOptions_1700_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*14, v_diag_1697_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*14 + 1, v_suppressElabErrors_1699_);
v___x_1706_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1703_);
lean_dec_ref(v_traces_1703_);
v_sz_1707_ = lean_array_size(v___x_1706_);
v___x_1708_ = ((size_t)0ULL);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(v_sz_1707_, v___x_1708_, v___x_1706_);
v_msg_1710_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1710_, 0, v_data_1677_);
lean_ctor_set(v_msg_1710_, 1, v_msg_1679_);
lean_ctor_set(v_msg_1710_, 2, v___x_1709_);
v___x_1711_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1710_, v___y_1680_, v___y_1681_, v___x_1705_, v___y_1683_);
lean_dec_ref(v___x_1705_);
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1749_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1749_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v_traceState_1717_; lean_object* v_env_1718_; lean_object* v_nextMacroScope_1719_; lean_object* v_ngen_1720_; lean_object* v_auxDeclNGen_1721_; lean_object* v_cache_1722_; lean_object* v_messages_1723_; lean_object* v_infoState_1724_; lean_object* v_snapshotTasks_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1748_; 
v___x_1716_ = lean_st_ref_take(v___y_1683_);
v_traceState_1717_ = lean_ctor_get(v___x_1716_, 4);
v_env_1718_ = lean_ctor_get(v___x_1716_, 0);
v_nextMacroScope_1719_ = lean_ctor_get(v___x_1716_, 1);
v_ngen_1720_ = lean_ctor_get(v___x_1716_, 2);
v_auxDeclNGen_1721_ = lean_ctor_get(v___x_1716_, 3);
v_cache_1722_ = lean_ctor_get(v___x_1716_, 5);
v_messages_1723_ = lean_ctor_get(v___x_1716_, 6);
v_infoState_1724_ = lean_ctor_get(v___x_1716_, 7);
v_snapshotTasks_1725_ = lean_ctor_get(v___x_1716_, 8);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1727_ = v___x_1716_;
v_isShared_1728_ = v_isSharedCheck_1748_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snapshotTasks_1725_);
lean_inc(v_infoState_1724_);
lean_inc(v_messages_1723_);
lean_inc(v_cache_1722_);
lean_inc(v_traceState_1717_);
lean_inc(v_auxDeclNGen_1721_);
lean_inc(v_ngen_1720_);
lean_inc(v_nextMacroScope_1719_);
lean_inc(v_env_1718_);
lean_dec(v___x_1716_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1748_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
uint64_t v_tid_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1746_; 
v_tid_1729_ = lean_ctor_get_uint64(v_traceState_1717_, sizeof(void*)*1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_traceState_1717_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v_traceState_1717_, 0);
lean_dec(v_unused_1747_);
v___x_1731_ = v_traceState_1717_;
v_isShared_1732_ = v_isSharedCheck_1746_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v_traceState_1717_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1746_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_ref_1678_);
lean_ctor_set(v___x_1733_, 1, v_a_1712_);
v___x_1734_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1676_, v___x_1733_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1734_);
v___x_1736_ = v___x_1731_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1734_);
lean_ctor_set_uint64(v_reuseFailAlloc_1745_, sizeof(void*)*1, v_tid_1729_);
v___x_1736_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 4, v___x_1736_);
v___x_1738_ = v___x_1727_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_env_1718_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_nextMacroScope_1719_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_ngen_1720_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_auxDeclNGen_1721_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1744_, 5, v_cache_1722_);
lean_ctor_set(v_reuseFailAlloc_1744_, 6, v_messages_1723_);
lean_ctor_set(v_reuseFailAlloc_1744_, 7, v_infoState_1724_);
lean_ctor_set(v_reuseFailAlloc_1744_, 8, v_snapshotTasks_1725_);
v___x_1738_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1739_ = lean_st_ref_set(v___y_1683_, v___x_1738_);
v___x_1740_ = lean_box(0);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1740_);
v___x_1742_ = v___x_1714_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_oldTraces_1750_, lean_object* v_data_1751_, lean_object* v_ref_1752_, lean_object* v_msg_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_oldTraces_1750_, v_data_1751_, v_ref_1752_, v_msg_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1759_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2));
v___x_1765_ = l_Lean_stringToMessageData(v___x_1764_);
return v___x_1765_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1766_; double v___x_1767_; 
v___x_1766_ = lean_unsigned_to_nat(1000u);
v___x_1767_ = lean_float_of_nat(v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1768_, uint8_t v_collapsed_1769_, lean_object* v_tag_1770_, lean_object* v_opts_1771_, uint8_t v_clsEnabled_1772_, lean_object* v_oldTraces_1773_, lean_object* v_msg_1774_, lean_object* v_resStartStop_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1880_; 
v_fst_1781_ = lean_ctor_get(v_resStartStop_1775_, 0);
v_snd_1782_ = lean_ctor_get(v_resStartStop_1775_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_resStartStop_1775_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1784_ = v_resStartStop_1775_;
v_isShared_1785_ = v_isSharedCheck_1880_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_inc(v_fst_1781_);
lean_dec(v_resStartStop_1775_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1880_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v_data_1789_; lean_object* v_fst_1800_; lean_object* v_snd_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1879_; 
v_fst_1800_ = lean_ctor_get(v_snd_1782_, 0);
v_snd_1801_ = lean_ctor_get(v_snd_1782_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_snd_1782_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1803_ = v_snd_1782_;
v_isShared_1804_ = v_isSharedCheck_1879_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_snd_1801_);
lean_inc(v_fst_1800_);
lean_dec(v_snd_1782_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1879_;
goto v_resetjp_1802_;
}
v___jp_1786_:
{
lean_object* v___x_1790_; 
lean_inc(v___y_1787_);
v___x_1790_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_oldTraces_1773_, v_data_1789_, v___y_1787_, v___y_1788_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref(v___x_1790_);
v___x_1791_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_fst_1781_);
return v___x_1791_;
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_fst_1781_);
v_a_1792_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1790_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; lean_object* v___y_1808_; lean_object* v_a_1809_; uint8_t v___y_1833_; double v___y_1864_; 
v___x_1805_ = l_Lean_trace_profiler;
v___x_1806_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1771_, v___x_1805_);
if (v___x_1806_ == 0)
{
v___y_1833_ = v___x_1806_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1870_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1771_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; double v___x_1873_; double v___x_1874_; double v___x_1875_; 
v___x_1871_ = l_Lean_trace_profiler_threshold;
v___x_1872_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1771_, v___x_1871_);
v___x_1873_ = lean_float_of_nat(v___x_1872_);
v___x_1874_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4);
v___x_1875_ = lean_float_div(v___x_1873_, v___x_1874_);
v___y_1864_ = v___x_1875_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; double v___x_1878_; 
v___x_1876_ = l_Lean_trace_profiler_threshold;
v___x_1877_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1771_, v___x_1876_);
v___x_1878_ = lean_float_of_nat(v___x_1877_);
v___y_1864_ = v___x_1878_;
goto v___jp_1863_;
}
}
v___jp_1807_:
{
uint8_t v_result_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v_result_1810_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_fst_1781_);
v___x_1811_ = l_Lean_TraceResult_toEmoji(v_result_1810_);
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
v___x_1813_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 7);
lean_ctor_set(v___x_1803_, 1, v___x_1813_);
lean_ctor_set(v___x_1803_, 0, v___x_1812_);
v___x_1815_ = v___x_1803_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v_m_1817_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 7);
lean_ctor_set(v___x_1784_, 1, v_a_1809_);
lean_ctor_set(v___x_1784_, 0, v___x_1815_);
v_m_1817_ = v___x_1784_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_a_1809_);
v_m_1817_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; double v___x_1820_; lean_object* v_data_1821_; 
v___x_1818_ = lean_box(v_result_1810_);
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
v___x_1820_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0);
lean_inc_ref(v_tag_1770_);
lean_inc_ref(v___x_1819_);
lean_inc(v_cls_1768_);
v_data_1821_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1821_, 0, v_cls_1768_);
lean_ctor_set(v_data_1821_, 1, v___x_1819_);
lean_ctor_set(v_data_1821_, 2, v_tag_1770_);
lean_ctor_set_float(v_data_1821_, sizeof(void*)*3, v___x_1820_);
lean_ctor_set_float(v_data_1821_, sizeof(void*)*3 + 8, v___x_1820_);
lean_ctor_set_uint8(v_data_1821_, sizeof(void*)*3 + 16, v_collapsed_1769_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v___x_1819_);
lean_dec(v_snd_1801_);
lean_dec(v_fst_1800_);
lean_dec_ref(v_tag_1770_);
lean_dec(v_cls_1768_);
v___y_1787_ = v___y_1808_;
v___y_1788_ = v_m_1817_;
v_data_1789_ = v_data_1821_;
goto v___jp_1786_;
}
else
{
lean_object* v_data_1822_; double v___x_1823_; double v___x_1824_; 
lean_dec_ref(v_data_1821_);
v_data_1822_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1822_, 0, v_cls_1768_);
lean_ctor_set(v_data_1822_, 1, v___x_1819_);
lean_ctor_set(v_data_1822_, 2, v_tag_1770_);
v___x_1823_ = lean_unbox_float(v_fst_1800_);
lean_dec(v_fst_1800_);
lean_ctor_set_float(v_data_1822_, sizeof(void*)*3, v___x_1823_);
v___x_1824_ = lean_unbox_float(v_snd_1801_);
lean_dec(v_snd_1801_);
lean_ctor_set_float(v_data_1822_, sizeof(void*)*3 + 8, v___x_1824_);
lean_ctor_set_uint8(v_data_1822_, sizeof(void*)*3 + 16, v_collapsed_1769_);
v___y_1787_ = v___y_1808_;
v___y_1788_ = v_m_1817_;
v_data_1789_ = v_data_1822_;
goto v___jp_1786_;
}
}
}
}
v___jp_1827_:
{
lean_object* v_ref_1828_; lean_object* v___x_1829_; 
v_ref_1828_ = lean_ctor_get(v___y_1778_, 5);
lean_inc(v___y_1779_);
lean_inc_ref(v___y_1778_);
lean_inc(v___y_1777_);
lean_inc_ref(v___y_1776_);
lean_inc(v_fst_1781_);
v___x_1829_ = lean_apply_6(v_msg_1774_, v_fst_1781_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, lean_box(0));
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref(v___x_1829_);
v___y_1808_ = v_ref_1828_;
v_a_1809_ = v_a_1830_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1831_; 
lean_dec_ref(v___x_1829_);
v___x_1831_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3);
v___y_1808_ = v_ref_1828_;
v_a_1809_ = v___x_1831_;
goto v___jp_1807_;
}
}
v___jp_1832_:
{
if (v_clsEnabled_1772_ == 0)
{
if (v___y_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v_traceState_1835_; lean_object* v_env_1836_; lean_object* v_nextMacroScope_1837_; lean_object* v_ngen_1838_; lean_object* v_auxDeclNGen_1839_; lean_object* v_cache_1840_; lean_object* v_messages_1841_; lean_object* v_infoState_1842_; lean_object* v_snapshotTasks_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1862_; 
lean_del_object(v___x_1803_);
lean_dec(v_snd_1801_);
lean_dec(v_fst_1800_);
lean_del_object(v___x_1784_);
lean_dec_ref(v_msg_1774_);
lean_dec_ref(v_tag_1770_);
lean_dec(v_cls_1768_);
v___x_1834_ = lean_st_ref_take(v___y_1779_);
v_traceState_1835_ = lean_ctor_get(v___x_1834_, 4);
v_env_1836_ = lean_ctor_get(v___x_1834_, 0);
v_nextMacroScope_1837_ = lean_ctor_get(v___x_1834_, 1);
v_ngen_1838_ = lean_ctor_get(v___x_1834_, 2);
v_auxDeclNGen_1839_ = lean_ctor_get(v___x_1834_, 3);
v_cache_1840_ = lean_ctor_get(v___x_1834_, 5);
v_messages_1841_ = lean_ctor_get(v___x_1834_, 6);
v_infoState_1842_ = lean_ctor_get(v___x_1834_, 7);
v_snapshotTasks_1843_ = lean_ctor_get(v___x_1834_, 8);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1845_ = v___x_1834_;
v_isShared_1846_ = v_isSharedCheck_1862_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_snapshotTasks_1843_);
lean_inc(v_infoState_1842_);
lean_inc(v_messages_1841_);
lean_inc(v_cache_1840_);
lean_inc(v_traceState_1835_);
lean_inc(v_auxDeclNGen_1839_);
lean_inc(v_ngen_1838_);
lean_inc(v_nextMacroScope_1837_);
lean_inc(v_env_1836_);
lean_dec(v___x_1834_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1862_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
uint64_t v_tid_1847_; lean_object* v_traces_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1861_; 
v_tid_1847_ = lean_ctor_get_uint64(v_traceState_1835_, sizeof(void*)*1);
v_traces_1848_ = lean_ctor_get(v_traceState_1835_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_traceState_1835_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1850_ = v_traceState_1835_;
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_traces_1848_);
lean_dec(v_traceState_1835_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1773_, v_traces_1848_);
lean_dec_ref(v_traces_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1852_);
lean_ctor_set_uint64(v_reuseFailAlloc_1860_, sizeof(void*)*1, v_tid_1847_);
v___x_1854_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 4, v___x_1854_);
v___x_1856_ = v___x_1845_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_env_1836_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_nextMacroScope_1837_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_ngen_1838_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_auxDeclNGen_1839_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1859_, 5, v_cache_1840_);
lean_ctor_set(v_reuseFailAlloc_1859_, 6, v_messages_1841_);
lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_infoState_1842_);
lean_ctor_set(v_reuseFailAlloc_1859_, 8, v_snapshotTasks_1843_);
v___x_1856_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_st_ref_set(v___y_1779_, v___x_1856_);
v___x_1858_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_fst_1781_);
return v___x_1858_;
}
}
}
}
}
else
{
goto v___jp_1827_;
}
}
else
{
goto v___jp_1827_;
}
}
v___jp_1863_:
{
double v___x_1865_; double v___x_1866_; double v___x_1867_; uint8_t v___x_1868_; 
v___x_1865_ = lean_unbox_float(v_snd_1801_);
v___x_1866_ = lean_unbox_float(v_fst_1800_);
v___x_1867_ = lean_float_sub(v___x_1865_, v___x_1866_);
v___x_1868_ = lean_float_decLt(v___y_1864_, v___x_1867_);
v___y_1833_ = v___x_1868_;
goto v___jp_1832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1881_, lean_object* v_collapsed_1882_, lean_object* v_tag_1883_, lean_object* v_opts_1884_, lean_object* v_clsEnabled_1885_, lean_object* v_oldTraces_1886_, lean_object* v_msg_1887_, lean_object* v_resStartStop_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v_collapsed_boxed_1894_; uint8_t v_clsEnabled_boxed_1895_; lean_object* v_res_1896_; 
v_collapsed_boxed_1894_ = lean_unbox(v_collapsed_1882_);
v_clsEnabled_boxed_1895_ = lean_unbox(v_clsEnabled_1885_);
v_res_1896_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1881_, v_collapsed_boxed_1894_, v_tag_1883_, v_opts_1884_, v_clsEnabled_boxed_1895_, v_oldTraces_1886_, v_msg_1887_, v_resStartStop_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec_ref(v_opts_1884_);
return v_res_1896_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1897_; double v___x_1898_; 
v___x_1897_ = lean_unsigned_to_nat(1000000000u);
v___x_1898_ = lean_float_of_nat(v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1899_, lean_object* v_numIndParams_1900_, lean_object* v_positions_1901_, lean_object* v_fnIndex_1902_, lean_object* v_recArg_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_options_1909_; uint8_t v_hasTrace_1910_; lean_object* v___x_1911_; lean_object* v___f_1912_; 
v_options_1909_ = lean_ctor_get(v_a_1906_, 2);
v_hasTrace_1910_ = lean_ctor_get_uint8(v_options_1909_, sizeof(void*)*1);
v___x_1911_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1899_);
lean_inc_ref(v_recArg_1903_);
v___f_1912_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1912_, 0, v___x_1911_);
lean_closure_set(v___f_1912_, 1, v_fnIndex_1902_);
lean_closure_set(v___f_1912_, 2, v_recArg_1903_);
lean_closure_set(v___f_1912_, 3, v_below_1899_);
if (v_hasTrace_1910_ == 0)
{
lean_object* v___x_1913_; 
lean_dec_ref(v_recArg_1903_);
v___x_1913_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1899_, v_numIndParams_1900_, v_positions_1901_, v___f_1912_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_a_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v_a_1922_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v_a_1938_; uint8_t v___x_1989_; 
v___x_1914_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1915_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg(v___x_1914_, v_a_1906_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
lean_inc_ref(v_below_1899_);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1917_, 0, v_below_1899_);
lean_closure_set(v___f_1917_, 1, v_recArg_1903_);
v___x_1918_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__1));
v___x_1989_ = lean_unbox(v_a_1916_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1990_ = l_Lean_trace_profiler;
v___x_1991_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1909_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
lean_dec_ref(v___f_1917_);
lean_dec(v_a_1916_);
v___x_1992_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1899_, v_numIndParams_1900_, v_positions_1901_, v___f_1912_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1992_;
}
else
{
goto v___jp_1948_;
}
}
else
{
goto v___jp_1948_;
}
v___jp_1919_:
{
lean_object* v___x_1923_; double v___x_1924_; double v___x_1925_; double v___x_1926_; double v___x_1927_; double v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; 
v___x_1923_ = lean_io_mono_nanos_now();
v___x_1924_ = lean_float_of_nat(v___y_1921_);
v___x_1925_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1926_ = lean_float_div(v___x_1924_, v___x_1925_);
v___x_1927_ = lean_float_of_nat(v___x_1923_);
v___x_1928_ = lean_float_div(v___x_1927_, v___x_1925_);
v___x_1929_ = lean_box_float(v___x_1926_);
v___x_1930_ = lean_box_float(v___x_1928_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1922_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_unbox(v_a_1916_);
lean_dec(v_a_1916_);
v___x_1934_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1914_, v_hasTrace_1910_, v___x_1918_, v_options_1909_, v___x_1933_, v___y_1920_, v___f_1917_, v___x_1932_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1934_;
}
v___jp_1935_:
{
lean_object* v___x_1939_; double v___x_1940_; double v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1939_ = lean_io_get_num_heartbeats();
v___x_1940_ = lean_float_of_nat(v___y_1937_);
v___x_1941_ = lean_float_of_nat(v___x_1939_);
v___x_1942_ = lean_box_float(v___x_1940_);
v___x_1943_ = lean_box_float(v___x_1941_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_a_1938_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_unbox(v_a_1916_);
lean_dec(v_a_1916_);
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1914_, v_hasTrace_1910_, v___x_1918_, v_options_1909_, v___x_1946_, v___y_1936_, v___f_1917_, v___x_1945_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1947_;
}
v___jp_1948_:
{
lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1949_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1907_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1952_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1909_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_io_mono_nanos_now();
v___x_1954_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1899_, v_numIndParams_1900_, v_positions_1901_, v___f_1912_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set_tag(v___x_1957_, 1);
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
v___y_1920_ = v_a_1950_;
v___y_1921_ = v___x_1953_;
v_a_1922_ = v___x_1960_;
goto v___jp_1919_;
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
v_a_1963_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1954_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1954_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 0);
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
v___y_1920_ = v_a_1950_;
v___y_1921_ = v___x_1953_;
v_a_1922_ = v___x_1968_;
goto v___jp_1919_;
}
}
}
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_io_get_num_heartbeats();
v___x_1972_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1899_, v_numIndParams_1900_, v_positions_1901_, v___f_1912_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 1);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
v___y_1936_ = v_a_1950_;
v___y_1937_ = v___x_1971_;
v_a_1938_ = v___x_1978_;
goto v___jp_1935_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1972_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1972_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 0);
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
v___y_1936_ = v_a_1950_;
v___y_1937_ = v___x_1971_;
v_a_1938_ = v___x_1986_;
goto v___jp_1935_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1993_, lean_object* v_numIndParams_1994_, lean_object* v_positions_1995_, lean_object* v_fnIndex_1996_, lean_object* v_recArg_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Elab_Structural_toBelow(v_below_1993_, v_numIndParams_1994_, v_positions_1995_, v_fnIndex_1996_, v_recArg_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_00_u03b1_2004_, lean_object* v_x_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_x_2005_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_x_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_00_u03b1_2012_, v_x_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_2020_, lean_object* v___y_2021_, lean_object* v_b_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; 
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2021_);
v___x_2028_ = lean_apply_7(v_k_2020_, v_b_2022_, v___y_2021_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, lean_box(0));
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_2029_, lean_object* v___y_2030_, lean_object* v_b_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_2029_, v___y_2030_, v_b_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2030_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_2038_, uint8_t v_bi_2039_, lean_object* v_type_2040_, lean_object* v_k_2041_, uint8_t v_kind_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___f_2049_; lean_object* v___x_2050_; 
lean_inc(v___y_2043_);
v___f_2049_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2049_, 0, v_k_2041_);
lean_closure_set(v___f_2049_, 1, v___y_2043_);
v___x_2050_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2038_, v_bi_2039_, v_type_2040_, v___f_2049_, v_kind_2042_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2050_) == 0)
{
return v___x_2050_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_2059_, lean_object* v_bi_2060_, lean_object* v_type_2061_, lean_object* v_k_2062_, lean_object* v_kind_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
uint8_t v_bi_boxed_2070_; uint8_t v_kind_boxed_2071_; lean_object* v_res_2072_; 
v_bi_boxed_2070_ = lean_unbox(v_bi_2060_);
v_kind_boxed_2071_ = lean_unbox(v_kind_2063_);
v_res_2072_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2059_, v_bi_boxed_2070_, v_type_2061_, v_k_2062_, v_kind_boxed_2071_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2073_, lean_object* v_name_2074_, uint8_t v_bi_2075_, lean_object* v_type_2076_, lean_object* v_k_2077_, uint8_t v_kind_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2074_, v_bi_2075_, v_type_2076_, v_k_2077_, v_kind_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2086_, lean_object* v_name_2087_, lean_object* v_bi_2088_, lean_object* v_type_2089_, lean_object* v_k_2090_, lean_object* v_kind_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v_bi_boxed_2098_; uint8_t v_kind_boxed_2099_; lean_object* v_res_2100_; 
v_bi_boxed_2098_ = lean_unbox(v_bi_2088_);
v_kind_boxed_2099_ = lean_unbox(v_kind_2091_);
v_res_2100_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2086_, v_name_2087_, v_bi_boxed_2098_, v_type_2089_, v_k_2090_, v_kind_boxed_2099_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(lean_object* v_cls_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_options_2104_; uint8_t v_hasTrace_2105_; 
v_options_2104_ = lean_ctor_get(v___y_2102_, 2);
v_hasTrace_2105_ = lean_ctor_get_uint8(v_options_2104_, sizeof(void*)*1);
if (v_hasTrace_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec(v_cls_2101_);
v___x_2106_ = lean_box(v_hasTrace_2105_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
else
{
lean_object* v_inheritedTraceOptions_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_inheritedTraceOptions_2108_ = lean_ctor_get(v___y_2102_, 13);
v___x_2109_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___redArg___closed__1));
v___x_2110_ = l_Lean_Name_append(v___x_2109_, v_cls_2101_);
v___x_2111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2108_, v_options_2104_, v___x_2110_);
lean_dec(v___x_2110_);
v___x_2112_ = lean_box(v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_cls_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v_cls_2114_, v___y_2115_);
lean_dec_ref(v___y_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_cls_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v_cls_2118_, v___y_2122_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___boxed(lean_object* v_cls_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v_cls_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0(lean_object* v_k_2134_, lean_object* v___y_2135_, lean_object* v_b_2136_, lean_object* v_c_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2135_);
v___x_2143_ = lean_apply_8(v_k_2134_, v_b_2136_, v_c_2137_, v___y_2135_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, lean_box(0));
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0___boxed(lean_object* v_k_2144_, lean_object* v___y_2145_, lean_object* v_b_2146_, lean_object* v_c_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0(v_k_2144_, v___y_2145_, v_b_2146_, v_c_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2145_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(lean_object* v_e_2154_, lean_object* v_maxFVars_2155_, lean_object* v_k_2156_, uint8_t v_cleanupAnnotations_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___f_2164_; uint8_t v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_inc(v___y_2158_);
v___f_2164_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2164_, 0, v_k_2156_);
lean_closure_set(v___f_2164_, 1, v___y_2158_);
v___x_2165_ = 1;
v___x_2166_ = 0;
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_maxFVars_2155_);
v___x_2168_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2154_, v___x_2165_, v___x_2166_, v___x_2165_, v___x_2166_, v___x_2167_, v___f_2164_, v_cleanupAnnotations_2157_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec_ref(v___x_2167_);
if (lean_obj_tag(v___x_2168_) == 0)
{
return v___x_2168_;
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg___boxed(lean_object* v_e_2177_, lean_object* v_maxFVars_2178_, lean_object* v_k_2179_, lean_object* v_cleanupAnnotations_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2187_; lean_object* v_res_2188_; 
v_cleanupAnnotations_boxed_2187_ = lean_unbox(v_cleanupAnnotations_2180_);
v_res_2188_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(v_e_2177_, v_maxFVars_2178_, v_k_2179_, v_cleanupAnnotations_boxed_2187_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_00_u03b1_2189_, lean_object* v_e_2190_, lean_object* v_maxFVars_2191_, lean_object* v_k_2192_, uint8_t v_cleanupAnnotations_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(v_e_2190_, v_maxFVars_2191_, v_k_2192_, v_cleanupAnnotations_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_00_u03b1_2201_, lean_object* v_e_2202_, lean_object* v_maxFVars_2203_, lean_object* v_k_2204_, lean_object* v_cleanupAnnotations_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2212_; lean_object* v_res_2213_; 
v_cleanupAnnotations_boxed_2212_ = lean_unbox(v_cleanupAnnotations_2205_);
v_res_2213_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_00_u03b1_2201_, v_e_2202_, v_maxFVars_2203_, v_k_2204_, v_cleanupAnnotations_boxed_2212_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_cls_2214_, lean_object* v_msg_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_ref_2221_; lean_object* v___x_2222_; lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2267_; 
v_ref_2221_ = lean_ctor_get(v___y_2218_, 5);
v___x_2222_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2267_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2267_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v_traceState_2228_; lean_object* v_env_2229_; lean_object* v_nextMacroScope_2230_; lean_object* v_ngen_2231_; lean_object* v_auxDeclNGen_2232_; lean_object* v_cache_2233_; lean_object* v_messages_2234_; lean_object* v_infoState_2235_; lean_object* v_snapshotTasks_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2266_; 
v___x_2227_ = lean_st_ref_take(v___y_2219_);
v_traceState_2228_ = lean_ctor_get(v___x_2227_, 4);
v_env_2229_ = lean_ctor_get(v___x_2227_, 0);
v_nextMacroScope_2230_ = lean_ctor_get(v___x_2227_, 1);
v_ngen_2231_ = lean_ctor_get(v___x_2227_, 2);
v_auxDeclNGen_2232_ = lean_ctor_get(v___x_2227_, 3);
v_cache_2233_ = lean_ctor_get(v___x_2227_, 5);
v_messages_2234_ = lean_ctor_get(v___x_2227_, 6);
v_infoState_2235_ = lean_ctor_get(v___x_2227_, 7);
v_snapshotTasks_2236_ = lean_ctor_get(v___x_2227_, 8);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2238_ = v___x_2227_;
v_isShared_2239_ = v_isSharedCheck_2266_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_snapshotTasks_2236_);
lean_inc(v_infoState_2235_);
lean_inc(v_messages_2234_);
lean_inc(v_cache_2233_);
lean_inc(v_traceState_2228_);
lean_inc(v_auxDeclNGen_2232_);
lean_inc(v_ngen_2231_);
lean_inc(v_nextMacroScope_2230_);
lean_inc(v_env_2229_);
lean_dec(v___x_2227_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2266_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
uint64_t v_tid_2240_; lean_object* v_traces_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2265_; 
v_tid_2240_ = lean_ctor_get_uint64(v_traceState_2228_, sizeof(void*)*1);
v_traces_2241_ = lean_ctor_get(v_traceState_2228_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_traceState_2228_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2243_ = v_traceState_2228_;
v_isShared_2244_ = v_isSharedCheck_2265_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_traces_2241_);
lean_dec(v_traceState_2228_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2265_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; double v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__0);
v___x_2247_ = 0;
v___x_2248_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__1));
v___x_2249_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2249_, 0, v_cls_2214_);
lean_ctor_set(v___x_2249_, 1, v___x_2245_);
lean_ctor_set(v___x_2249_, 2, v___x_2248_);
lean_ctor_set_float(v___x_2249_, sizeof(void*)*3, v___x_2246_);
lean_ctor_set_float(v___x_2249_, sizeof(void*)*3 + 8, v___x_2246_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*3 + 16, v___x_2247_);
v___x_2250_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___closed__2));
v___x_2251_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v_a_2223_);
lean_ctor_set(v___x_2251_, 2, v___x_2250_);
lean_inc(v_ref_2221_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_ref_2221_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = l_Lean_PersistentArray_push___redArg(v_traces_2241_, v___x_2252_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2253_);
v___x_2255_ = v___x_2243_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2253_);
lean_ctor_set_uint64(v_reuseFailAlloc_2264_, sizeof(void*)*1, v_tid_2240_);
v___x_2255_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2257_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 4, v___x_2255_);
v___x_2257_ = v___x_2238_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_env_2229_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_nextMacroScope_2230_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_ngen_2231_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_auxDeclNGen_2232_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2263_, 5, v_cache_2233_);
lean_ctor_set(v_reuseFailAlloc_2263_, 6, v_messages_2234_);
lean_ctor_set(v_reuseFailAlloc_2263_, 7, v_infoState_2235_);
lean_ctor_set(v_reuseFailAlloc_2263_, 8, v_snapshotTasks_2236_);
v___x_2257_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2258_ = lean_st_ref_set(v___y_2219_, v___x_2257_);
v___x_2259_ = lean_box(0);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2259_);
v___x_2261_ = v___x_2225_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_cls_2268_, lean_object* v_msg_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_cls_2268_, v_msg_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
return v_res_2275_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2276_, lean_object* v_as_2277_, size_t v_i_2278_, size_t v_stop_2279_){
_start:
{
uint8_t v___x_2280_; 
v___x_2280_ = lean_usize_dec_eq(v_i_2278_, v_stop_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v_fnName_2282_; lean_object* v_recArgPos_2283_; uint8_t v___x_2284_; 
v___x_2281_ = lean_array_uget_borrowed(v_as_2277_, v_i_2278_);
v_fnName_2282_ = lean_ctor_get(v___x_2281_, 0);
v_recArgPos_2283_ = lean_ctor_get(v___x_2281_, 2);
lean_inc(v_recArgPos_2283_);
lean_inc(v_fnName_2282_);
v___x_2284_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2282_, v_recArgPos_2283_, v_e_2276_);
if (v___x_2284_ == 0)
{
size_t v___x_2285_; size_t v___x_2286_; 
v___x_2285_ = ((size_t)1ULL);
v___x_2286_ = lean_usize_add(v_i_2278_, v___x_2285_);
v_i_2278_ = v___x_2286_;
goto _start;
}
else
{
return v___x_2284_;
}
}
else
{
uint8_t v___x_2288_; 
v___x_2288_ = 0;
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2289_, lean_object* v_as_2290_, lean_object* v_i_2291_, lean_object* v_stop_2292_){
_start:
{
size_t v_i_boxed_2293_; size_t v_stop_boxed_2294_; uint8_t v_res_2295_; lean_object* v_r_2296_; 
v_i_boxed_2293_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_stop_boxed_2294_ = lean_unbox_usize(v_stop_2292_);
lean_dec(v_stop_2292_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2289_, v_as_2290_, v_i_boxed_2293_, v_stop_boxed_2294_);
lean_dec_ref(v_as_2290_);
lean_dec_ref(v_e_2289_);
v_r_2296_ = lean_box(v_res_2295_);
return v_r_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; lean_object* v_env_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = lean_st_ref_get(v___y_2298_);
v_env_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc_ref(v_env_2301_);
lean_dec(v___x_2300_);
v___x_2302_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2301_, v_declName_2297_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2304_, v___y_2305_);
lean_dec(v___y_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v_toApplicative_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2378_; 
v___x_2315_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v___x_2315_, 1);
lean_dec(v_unused_2379_);
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2378_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_toApplicative_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2378_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_toFunctor_2320_; lean_object* v_toSeq_2321_; lean_object* v_toSeqLeft_2322_; lean_object* v_toSeqRight_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2376_; 
v_toFunctor_2320_ = lean_ctor_get(v_toApplicative_2316_, 0);
v_toSeq_2321_ = lean_ctor_get(v_toApplicative_2316_, 2);
v_toSeqLeft_2322_ = lean_ctor_get(v_toApplicative_2316_, 3);
v_toSeqRight_2323_ = lean_ctor_get(v_toApplicative_2316_, 4);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_toApplicative_2316_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_toApplicative_2316_, 1);
lean_dec(v_unused_2377_);
v___x_2325_ = v_toApplicative_2316_;
v_isShared_2326_ = v_isSharedCheck_2376_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_toSeqRight_2323_);
lean_inc(v_toSeqLeft_2322_);
lean_inc(v_toSeq_2321_);
lean_inc(v_toFunctor_2320_);
lean_dec(v_toApplicative_2316_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2376_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___f_2327_; lean_object* v___f_2328_; lean_object* v___f_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___x_2336_; 
v___f_2327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2328_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref(v_toFunctor_2320_);
v___f_2329_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2329_, 0, v_toFunctor_2320_);
v___f_2330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2330_, 0, v_toFunctor_2320_);
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___f_2329_);
lean_ctor_set(v___x_2331_, 1, v___f_2330_);
v___f_2332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2332_, 0, v_toSeqRight_2323_);
v___f_2333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2333_, 0, v_toSeqLeft_2322_);
v___f_2334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2334_, 0, v_toSeq_2321_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 4, v___f_2332_);
lean_ctor_set(v___x_2325_, 3, v___f_2333_);
lean_ctor_set(v___x_2325_, 2, v___f_2334_);
lean_ctor_set(v___x_2325_, 1, v___f_2327_);
lean_ctor_set(v___x_2325_, 0, v___x_2331_);
v___x_2336_ = v___x_2325_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___f_2327_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v___f_2334_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v___f_2333_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v___f_2332_);
v___x_2336_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 1, v___f_2328_);
lean_ctor_set(v___x_2318_, 0, v___x_2336_);
v___x_2338_ = v___x_2318_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v___f_2328_);
v___x_2338_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; lean_object* v_toApplicative_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2372_; 
v___x_2339_ = l_StateRefT_x27_instMonad___redArg(v___x_2338_);
v_toApplicative_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v___x_2339_, 1);
lean_dec(v_unused_2373_);
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2372_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_toApplicative_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2372_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v_toFunctor_2344_; lean_object* v_toSeq_2345_; lean_object* v_toSeqLeft_2346_; lean_object* v_toSeqRight_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2370_; 
v_toFunctor_2344_ = lean_ctor_get(v_toApplicative_2340_, 0);
v_toSeq_2345_ = lean_ctor_get(v_toApplicative_2340_, 2);
v_toSeqLeft_2346_ = lean_ctor_get(v_toApplicative_2340_, 3);
v_toSeqRight_2347_ = lean_ctor_get(v_toApplicative_2340_, 4);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_toApplicative_2340_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v_toApplicative_2340_, 1);
lean_dec(v_unused_2371_);
v___x_2349_ = v_toApplicative_2340_;
v_isShared_2350_ = v_isSharedCheck_2370_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_toSeqRight_2347_);
lean_inc(v_toSeqLeft_2346_);
lean_inc(v_toSeq_2345_);
lean_inc(v_toFunctor_2344_);
lean_dec(v_toApplicative_2340_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2370_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___f_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; lean_object* v___f_2356_; lean_object* v___f_2357_; lean_object* v___f_2358_; lean_object* v___x_2360_; 
v___f_2351_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2352_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2344_);
v___f_2353_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2353_, 0, v_toFunctor_2344_);
v___f_2354_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2354_, 0, v_toFunctor_2344_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___f_2353_);
lean_ctor_set(v___x_2355_, 1, v___f_2354_);
v___f_2356_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2356_, 0, v_toSeqRight_2347_);
v___f_2357_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2357_, 0, v_toSeqLeft_2346_);
v___f_2358_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2358_, 0, v_toSeq_2345_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v___f_2356_);
lean_ctor_set(v___x_2349_, 3, v___f_2357_);
lean_ctor_set(v___x_2349_, 2, v___f_2358_);
lean_ctor_set(v___x_2349_, 1, v___f_2351_);
lean_ctor_set(v___x_2349_, 0, v___x_2355_);
v___x_2360_ = v___x_2349_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___f_2351_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v___f_2358_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v___f_2357_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v___f_2356_);
v___x_2360_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 1, v___f_2352_);
lean_ctor_set(v___x_2342_, 0, v___x_2360_);
v___x_2362_ = v___x_2342_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v___f_2352_);
v___x_2362_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_26053__overap_2366_; lean_object* v___x_2367_; 
v___x_2363_ = l_StateRefT_x27_instMonad___redArg(v___x_2362_);
v___x_2364_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2365_ = l_instInhabitedOfMonad___redArg(v___x_2363_, v___x_2364_);
v___x_26053__overap_2366_ = lean_panic_fn(v___x_2365_, v_msg_2308_);
lean_inc(v___y_2313_);
lean_inc_ref(v___y_2312_);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
v___x_2367_ = lean_apply_6(v___x_26053__overap_2366_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, lean_box(0));
return v___x_2367_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
return v_res_2387_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
lean_ctor_set(v___x_2393_, 3, v___x_2391_);
lean_ctor_set(v___x_2393_, 4, v___x_2391_);
lean_ctor_set(v___x_2393_, 5, v___x_2391_);
lean_ctor_set(v___x_2393_, 6, v___x_2391_);
lean_ctor_set(v___x_2393_, 7, v___x_2391_);
lean_ctor_set(v___x_2393_, 8, v___x_2391_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_unsigned_to_nat(32u);
v___x_2395_ = lean_mk_empty_array_with_capacity(v___x_2394_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2397_ = ((size_t)5ULL);
v___x_2398_ = lean_unsigned_to_nat(0u);
v___x_2399_ = lean_unsigned_to_nat(32u);
v___x_2400_ = lean_mk_empty_array_with_capacity(v___x_2399_);
v___x_2401_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_2402_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v___x_2400_);
lean_ctor_set(v___x_2402_, 2, v___x_2398_);
lean_ctor_set(v___x_2402_, 3, v___x_2398_);
lean_ctor_set_usize(v___x_2402_, 4, v___x_2397_);
return v___x_2402_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2403_ = lean_box(1);
v___x_2404_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_2405_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_2406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v___x_2404_);
lean_ctor_set(v___x_2406_, 2, v___x_2403_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_2409_ = l_Lean_stringToMessageData(v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
return v___x_2415_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__14));
v___x_2421_ = l_Lean_stringToMessageData(v___x_2420_);
return v___x_2421_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__16));
v___x_2424_ = l_Lean_stringToMessageData(v___x_2423_);
return v___x_2424_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__18));
v___x_2427_ = l_Lean_stringToMessageData(v___x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_2428_, lean_object* v_declHint_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; lean_object* v_env_2433_; uint8_t v___x_2434_; 
v___x_2432_ = lean_st_ref_get(v___y_2430_);
v_env_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc_ref(v_env_2433_);
lean_dec(v___x_2432_);
v___x_2434_ = l_Lean_Name_isAnonymous(v_declHint_2429_);
if (v___x_2434_ == 0)
{
uint8_t v_isExporting_2435_; 
v_isExporting_2435_ = lean_ctor_get_uint8(v_env_2433_, sizeof(void*)*8);
if (v_isExporting_2435_ == 0)
{
lean_object* v___x_2436_; 
lean_dec_ref(v_env_2433_);
lean_dec(v_declHint_2429_);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_msg_2428_);
return v___x_2436_;
}
else
{
lean_object* v___x_2437_; uint8_t v___x_2438_; 
lean_inc_ref(v_env_2433_);
v___x_2437_ = l_Lean_Environment_setExporting(v_env_2433_, v___x_2434_);
lean_inc(v_declHint_2429_);
lean_inc_ref(v___x_2437_);
v___x_2438_ = l_Lean_Environment_contains(v___x_2437_, v_declHint_2429_, v_isExporting_2435_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_dec_ref(v___x_2437_);
lean_dec_ref(v_env_2433_);
lean_dec(v_declHint_2429_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v_msg_2428_);
return v___x_2439_;
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_c_2445_; lean_object* v___x_2446_; 
v___x_2440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_2441_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_2442_ = l_Lean_Options_empty;
v___x_2443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2437_);
lean_ctor_set(v___x_2443_, 1, v___x_2440_);
lean_ctor_set(v___x_2443_, 2, v___x_2441_);
lean_ctor_set(v___x_2443_, 3, v___x_2442_);
lean_inc(v_declHint_2429_);
v___x_2444_ = l_Lean_MessageData_ofConstName(v_declHint_2429_, v___x_2434_);
v_c_2445_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2445_, 0, v___x_2443_);
lean_ctor_set(v_c_2445_, 1, v___x_2444_);
v___x_2446_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2433_, v_declHint_2429_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_dec_ref(v_env_2433_);
lean_dec(v_declHint_2429_);
v___x_2447_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v_c_2445_);
v___x_2449_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = l_Lean_MessageData_note(v___x_2450_);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_msg_2428_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
else
{
lean_object* v_val_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2489_; 
v_val_2454_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2456_ = v___x_2446_;
v_isShared_2457_ = v_isSharedCheck_2489_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_val_2454_);
lean_dec(v___x_2446_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2489_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_mod_2461_; uint8_t v___x_2462_; 
v___x_2458_ = lean_box(0);
v___x_2459_ = l_Lean_Environment_header(v_env_2433_);
lean_dec_ref(v_env_2433_);
v___x_2460_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2459_);
v_mod_2461_ = lean_array_get(v___x_2458_, v___x_2460_, v_val_2454_);
lean_dec(v_val_2454_);
lean_dec_ref(v___x_2460_);
v___x_2462_ = l_Lean_isPrivateName(v_declHint_2429_);
lean_dec(v_declHint_2429_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2463_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v_c_2445_);
v___x_2465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_MessageData_ofName(v_mod_2461_);
v___x_2468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__15);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l_Lean_MessageData_note(v___x_2470_);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v_msg_2428_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set_tag(v___x_2456_, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2472_);
v___x_2474_ = v___x_2456_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2476_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
lean_ctor_set(v___x_2477_, 1, v_c_2445_);
v___x_2478_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__17);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l_Lean_MessageData_ofName(v_mod_2461_);
v___x_2481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___closed__19);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_MessageData_note(v___x_2483_);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v_msg_2428_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set_tag(v___x_2456_, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2485_);
v___x_2487_ = v___x_2456_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2490_; 
lean_dec_ref(v_env_2433_);
lean_dec(v_declHint_2429_);
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_msg_2428_);
return v___x_2490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_2491_, lean_object* v_declHint_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_2491_, v_declHint_2492_, v___y_2493_);
lean_dec(v___y_2493_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19(lean_object* v_msg_2496_, lean_object* v_declHint_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2514_; 
v___x_2504_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_2496_, v_declHint_2497_, v___y_2502_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2514_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2514_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2509_ = l_Lean_unknownIdentifierMessageTag;
v___x_2510_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v_a_2505_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2510_);
v___x_2512_ = v___x_2507_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_2515_, lean_object* v_declHint_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19(v_msg_2515_, v_declHint_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_ref_2530_; lean_object* v___x_2531_; lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2540_; 
v_ref_2530_ = lean_ctor_get(v___y_2527_, 5);
v___x_2531_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2540_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2540_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_inc(v_ref_2530_);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_ref_2530_);
lean_ctor_set(v___x_2536_, 1, v_a_2532_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set_tag(v___x_2534_, 1);
lean_ctor_set(v___x_2534_, 0, v___x_2536_);
v___x_2538_ = v___x_2534_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_2548_, lean_object* v_msg_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_fileName_2556_; lean_object* v_fileMap_2557_; lean_object* v_options_2558_; lean_object* v_currRecDepth_2559_; lean_object* v_maxRecDepth_2560_; lean_object* v_ref_2561_; lean_object* v_currNamespace_2562_; lean_object* v_openDecls_2563_; lean_object* v_initHeartbeats_2564_; lean_object* v_maxHeartbeats_2565_; lean_object* v_quotContext_2566_; lean_object* v_currMacroScope_2567_; uint8_t v_diag_2568_; lean_object* v_cancelTk_x3f_2569_; uint8_t v_suppressElabErrors_2570_; lean_object* v_inheritedTraceOptions_2571_; lean_object* v_ref_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_fileName_2556_ = lean_ctor_get(v___y_2553_, 0);
v_fileMap_2557_ = lean_ctor_get(v___y_2553_, 1);
v_options_2558_ = lean_ctor_get(v___y_2553_, 2);
v_currRecDepth_2559_ = lean_ctor_get(v___y_2553_, 3);
v_maxRecDepth_2560_ = lean_ctor_get(v___y_2553_, 4);
v_ref_2561_ = lean_ctor_get(v___y_2553_, 5);
v_currNamespace_2562_ = lean_ctor_get(v___y_2553_, 6);
v_openDecls_2563_ = lean_ctor_get(v___y_2553_, 7);
v_initHeartbeats_2564_ = lean_ctor_get(v___y_2553_, 8);
v_maxHeartbeats_2565_ = lean_ctor_get(v___y_2553_, 9);
v_quotContext_2566_ = lean_ctor_get(v___y_2553_, 10);
v_currMacroScope_2567_ = lean_ctor_get(v___y_2553_, 11);
v_diag_2568_ = lean_ctor_get_uint8(v___y_2553_, sizeof(void*)*14);
v_cancelTk_x3f_2569_ = lean_ctor_get(v___y_2553_, 12);
v_suppressElabErrors_2570_ = lean_ctor_get_uint8(v___y_2553_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2571_ = lean_ctor_get(v___y_2553_, 13);
v_ref_2572_ = l_Lean_replaceRef(v_ref_2548_, v_ref_2561_);
lean_inc_ref(v_inheritedTraceOptions_2571_);
lean_inc(v_cancelTk_x3f_2569_);
lean_inc(v_currMacroScope_2567_);
lean_inc(v_quotContext_2566_);
lean_inc(v_maxHeartbeats_2565_);
lean_inc(v_initHeartbeats_2564_);
lean_inc(v_openDecls_2563_);
lean_inc(v_currNamespace_2562_);
lean_inc(v_maxRecDepth_2560_);
lean_inc(v_currRecDepth_2559_);
lean_inc_ref(v_options_2558_);
lean_inc_ref(v_fileMap_2557_);
lean_inc_ref(v_fileName_2556_);
v___x_2573_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2573_, 0, v_fileName_2556_);
lean_ctor_set(v___x_2573_, 1, v_fileMap_2557_);
lean_ctor_set(v___x_2573_, 2, v_options_2558_);
lean_ctor_set(v___x_2573_, 3, v_currRecDepth_2559_);
lean_ctor_set(v___x_2573_, 4, v_maxRecDepth_2560_);
lean_ctor_set(v___x_2573_, 5, v_ref_2572_);
lean_ctor_set(v___x_2573_, 6, v_currNamespace_2562_);
lean_ctor_set(v___x_2573_, 7, v_openDecls_2563_);
lean_ctor_set(v___x_2573_, 8, v_initHeartbeats_2564_);
lean_ctor_set(v___x_2573_, 9, v_maxHeartbeats_2565_);
lean_ctor_set(v___x_2573_, 10, v_quotContext_2566_);
lean_ctor_set(v___x_2573_, 11, v_currMacroScope_2567_);
lean_ctor_set(v___x_2573_, 12, v_cancelTk_x3f_2569_);
lean_ctor_set(v___x_2573_, 13, v_inheritedTraceOptions_2571_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*14, v_diag_2568_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*14 + 1, v_suppressElabErrors_2570_);
v___x_2574_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2549_, v___y_2551_, v___y_2552_, v___x_2573_, v___y_2554_);
lean_dec_ref(v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_2575_, lean_object* v_msg_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(v_ref_2575_, v_msg_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v_ref_2575_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(lean_object* v_ref_2584_, lean_object* v_msg_2585_, lean_object* v_declHint_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; lean_object* v_a_2594_; lean_object* v___x_2595_; 
v___x_2593_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19(v_msg_2585_, v_declHint_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2593_);
v___x_2595_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(v_ref_2584_, v_a_2594_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg___boxed(lean_object* v_ref_2596_, lean_object* v_msg_2597_, lean_object* v_declHint_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(v_ref_2596_, v_msg_2597_, v_declHint_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec(v_ref_2596_);
return v_res_2605_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__0));
v___x_2608_ = l_Lean_stringToMessageData(v___x_2607_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__2));
v___x_2611_ = l_Lean_stringToMessageData(v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(lean_object* v_ref_2612_, lean_object* v_constName_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2620_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__1);
v___x_2621_ = 0;
lean_inc(v_constName_2613_);
v___x_2622_ = l_Lean_MessageData_ofConstName(v_constName_2613_, v___x_2621_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2620_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___closed__3);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(v_ref_2612_, v___x_2625_, v_constName_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg___boxed(lean_object* v_ref_2627_, lean_object* v_constName_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(v_ref_2627_, v_constName_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec(v_ref_2627_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(lean_object* v_constName_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_ref_2643_; lean_object* v___x_2644_; 
v_ref_2643_ = lean_ctor_get(v___y_2640_, 5);
v___x_2644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(v_ref_2643_, v_constName_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_constName_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(v_constName_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; lean_object* v_env_2661_; uint8_t v___x_2662_; lean_object* v___x_2663_; 
v___x_2660_ = lean_st_ref_get(v___y_2658_);
v_env_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc_ref(v_env_2661_);
lean_dec(v___x_2660_);
v___x_2662_ = 0;
lean_inc(v_constName_2653_);
v___x_2663_ = l_Lean_Environment_find_x3f(v_env_2661_, v_constName_2653_, v___x_2662_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(v_constName_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
return v___x_2664_;
}
else
{
lean_object* v_val_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_constName_2653_);
v_val_2665_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2663_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_val_2665_);
lean_dec(v___x_2663_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set_tag(v___x_2667_, 0);
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_val_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
return v_res_2680_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2685_ = lean_unsigned_to_nat(53u);
v___x_2686_ = lean_unsigned_to_nat(62u);
v___x_2687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2689_ = l_mkPanicMessageWithDecl(v___x_2688_, v___x_2687_, v___x_2686_, v___x_2685_, v___x_2684_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2690_, size_t v_i_2691_, lean_object* v_bs_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_usize_dec_lt(v_i_2691_, v_sz_2690_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_bs_2692_);
return v___x_2700_;
}
else
{
lean_object* v_v_2701_; lean_object* v___x_2702_; 
v_v_2701_ = lean_array_uget_borrowed(v_bs_2692_, v_i_2691_);
lean_inc(v_v_2701_);
v___x_2702_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2701_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; lean_object* v_bs_x27_2705_; lean_object* v_a_2707_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___x_2702_);
v___x_2704_ = lean_unsigned_to_nat(0u);
v_bs_x27_2705_ = lean_array_uset(v_bs_2692_, v_i_2691_, v___x_2704_);
if (lean_obj_tag(v_a_2703_) == 6)
{
lean_object* v_val_2712_; lean_object* v_numFields_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; 
v_val_2712_ = lean_ctor_get(v_a_2703_, 0);
lean_inc_ref(v_val_2712_);
lean_dec_ref(v_a_2703_);
v_numFields_2713_ = lean_ctor_get(v_val_2712_, 4);
lean_inc(v_numFields_2713_);
lean_dec_ref(v_val_2712_);
v___x_2714_ = 0;
v___x_2715_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2715_, 0, v_numFields_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2704_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*2, v___x_2714_);
v_a_2707_ = v___x_2715_;
goto v___jp_2706_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec(v_a_2703_);
v___x_2716_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2717_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2716_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref(v___x_2717_);
v_a_2707_ = v_a_2718_;
goto v___jp_2706_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec_ref(v_bs_x27_2705_);
v_a_2719_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2717_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2717_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
v___jp_2706_:
{
size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = ((size_t)1ULL);
v___x_2709_ = lean_usize_add(v_i_2691_, v___x_2708_);
v___x_2710_ = lean_array_uset(v_bs_x27_2705_, v_i_2691_, v_a_2707_);
v_i_2691_ = v___x_2709_;
v_bs_2692_ = v___x_2710_;
goto _start;
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref(v_bs_2692_);
v_a_2727_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2702_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2702_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2735_, lean_object* v_i_2736_, lean_object* v_bs_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
size_t v_sz_boxed_2744_; size_t v_i_boxed_2745_; lean_object* v_res_2746_; 
v_sz_boxed_2744_ = lean_unbox_usize(v_sz_2735_);
lean_dec(v_sz_2735_);
v_i_boxed_2745_ = lean_unbox_usize(v_i_2736_);
lean_dec(v_i_2736_);
v_res_2746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2744_, v_i_boxed_2745_, v_bs_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
return v_res_2746_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_unsigned_to_nat(16u);
v___x_2749_ = lean_mk_array(v___x_2748_, v___x_2747_);
return v___x_2749_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v___x_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2755_, uint8_t v_alsoCasesOn_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v___x_2766_; 
v___x_2766_ = l_Lean_Expr_isApp(v_e_2755_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec_ref(v_e_2755_);
v___x_2767_ = lean_box(0);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
else
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Expr_getAppFn(v_e_2755_);
if (lean_obj_tag(v___x_2769_) == 4)
{
lean_object* v_declName_2770_; lean_object* v_us_2771_; lean_object* v___x_2772_; lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2927_; 
v_declName_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_declName_2770_);
v_us_2771_ = lean_ctor_get(v___x_2769_, 1);
lean_inc(v_us_2771_);
lean_dec_ref(v___x_2769_);
lean_inc(v_declName_2770_);
v___x_2772_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2770_, v___y_2761_);
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2775_ = v___x_2772_;
v_isShared_2776_ = v_isSharedCheck_2927_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2927_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
if (lean_obj_tag(v_a_2773_) == 1)
{
lean_object* v_val_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2819_; 
v_val_2777_ = lean_ctor_get(v_a_2773_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_a_2773_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2779_ = v_a_2773_;
v_isShared_2780_ = v_isSharedCheck_2819_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_val_2777_);
lean_dec(v_a_2773_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2819_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_dummy_2781_; lean_object* v_nargs_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_args_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v_dummy_2781_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
v_nargs_2782_ = l_Lean_Expr_getAppNumArgs(v_e_2755_);
lean_inc(v_nargs_2782_);
v___x_2783_ = lean_mk_array(v_nargs_2782_, v_dummy_2781_);
v___x_2784_ = lean_unsigned_to_nat(1u);
v___x_2785_ = lean_nat_sub(v_nargs_2782_, v___x_2784_);
lean_dec(v_nargs_2782_);
v_args_2786_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2755_, v___x_2783_, v___x_2785_);
v___x_2787_ = lean_array_get_size(v_args_2786_);
v___x_2788_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2777_);
v___x_2789_ = lean_nat_dec_lt(v___x_2787_, v___x_2788_);
lean_dec(v___x_2788_);
if (v___x_2789_ == 0)
{
lean_object* v_numParams_2790_; lean_object* v_numDiscrs_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v_numParams_2790_ = lean_ctor_get(v_val_2777_, 0);
v_numDiscrs_2791_ = lean_ctor_get(v_val_2777_, 1);
v___x_2792_ = lean_array_mk(v_us_2771_);
v___x_2793_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2790_);
v___x_2794_ = l_Array_extract___redArg(v_args_2786_, v___x_2793_, v_numParams_2790_);
v___x_2795_ = l_Lean_instInhabitedExpr;
v___x_2796_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2777_);
v___x_2797_ = lean_array_get(v___x_2795_, v_args_2786_, v___x_2796_);
lean_dec(v___x_2796_);
v___x_2798_ = lean_nat_add(v_numParams_2790_, v___x_2784_);
v___x_2799_ = lean_nat_add(v___x_2798_, v_numDiscrs_2791_);
lean_inc(v___x_2799_);
lean_inc_ref(v_args_2786_);
v___x_2800_ = l_Array_toSubarray___redArg(v_args_2786_, v___x_2798_, v___x_2799_);
v___x_2801_ = l_Subarray_copy___redArg(v___x_2800_);
v___x_2802_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2777_);
v___x_2803_ = lean_nat_add(v___x_2799_, v___x_2802_);
lean_dec(v___x_2802_);
lean_inc(v___x_2803_);
lean_inc_ref(v_args_2786_);
v___x_2804_ = l_Array_toSubarray___redArg(v_args_2786_, v___x_2799_, v___x_2803_);
v___x_2805_ = l_Subarray_copy___redArg(v___x_2804_);
v___x_2806_ = l_Array_toSubarray___redArg(v_args_2786_, v___x_2803_, v___x_2787_);
v___x_2807_ = l_Subarray_copy___redArg(v___x_2806_);
v___x_2808_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2808_, 0, v_val_2777_);
lean_ctor_set(v___x_2808_, 1, v_declName_2770_);
lean_ctor_set(v___x_2808_, 2, v___x_2792_);
lean_ctor_set(v___x_2808_, 3, v___x_2794_);
lean_ctor_set(v___x_2808_, 4, v___x_2797_);
lean_ctor_set(v___x_2808_, 5, v___x_2801_);
lean_ctor_set(v___x_2808_, 6, v___x_2805_);
lean_ctor_set(v___x_2808_, 7, v___x_2807_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2808_);
v___x_2810_ = v___x_2779_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2812_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2810_);
v___x_2812_ = v___x_2775_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_dec_ref(v_args_2786_);
lean_del_object(v___x_2779_);
lean_dec(v_val_2777_);
lean_dec(v_us_2771_);
lean_dec(v_declName_2770_);
v___x_2815_ = lean_box(0);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2815_);
v___x_2817_ = v___x_2775_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v___x_2820_; 
lean_del_object(v___x_2775_);
lean_dec(v_a_2773_);
v___x_2820_ = lean_st_ref_get(v___y_2761_);
if (v_alsoCasesOn_2756_ == 0)
{
lean_dec(v___x_2820_);
lean_dec(v_us_2771_);
lean_dec(v_declName_2770_);
lean_dec_ref(v_e_2755_);
goto v___jp_2763_;
}
else
{
lean_object* v_env_2821_; uint8_t v___x_2822_; 
v_env_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc_ref(v_env_2821_);
lean_dec(v___x_2820_);
lean_inc(v_declName_2770_);
v___x_2822_ = l_Lean_isCasesOnRecursor(v_env_2821_, v_declName_2770_);
if (v___x_2822_ == 0)
{
lean_dec(v_us_2771_);
lean_dec(v_declName_2770_);
lean_dec_ref(v_e_2755_);
goto v___jp_2763_;
}
else
{
lean_object* v_indName_2823_; lean_object* v___x_2824_; 
v_indName_2823_ = l_Lean_Name_getPrefix(v_declName_2770_);
v___x_2824_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2823_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2918_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2918_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2918_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
if (lean_obj_tag(v_a_2825_) == 5)
{
lean_object* v_val_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2913_; 
v_val_2829_ = lean_ctor_get(v_a_2825_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_a_2825_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2831_ = v_a_2825_;
v_isShared_2832_ = v_isSharedCheck_2913_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_val_2829_);
lean_dec(v_a_2825_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2913_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v_toConstantVal_2833_; lean_object* v_numParams_2834_; lean_object* v_numIndices_2835_; lean_object* v_ctors_2836_; lean_object* v_nargs_2837_; lean_object* v_dummy_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_args_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_toConstantVal_2833_ = lean_ctor_get(v_val_2829_, 0);
lean_inc_ref(v_toConstantVal_2833_);
v_numParams_2834_ = lean_ctor_get(v_val_2829_, 1);
lean_inc(v_numParams_2834_);
v_numIndices_2835_ = lean_ctor_get(v_val_2829_, 2);
lean_inc(v_numIndices_2835_);
v_ctors_2836_ = lean_ctor_get(v_val_2829_, 4);
lean_inc(v_ctors_2836_);
v_nargs_2837_ = l_Lean_Expr_getAppNumArgs(v_e_2755_);
v_dummy_2838_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
lean_inc(v_nargs_2837_);
v___x_2839_ = lean_mk_array(v_nargs_2837_, v_dummy_2838_);
v___x_2840_ = lean_unsigned_to_nat(1u);
v___x_2841_ = lean_nat_sub(v_nargs_2837_, v___x_2840_);
lean_dec(v_nargs_2837_);
v_args_2842_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2755_, v___x_2839_, v___x_2841_);
v___x_2843_ = lean_nat_add(v_numParams_2834_, v___x_2840_);
v___x_2844_ = lean_nat_add(v___x_2843_, v_numIndices_2835_);
v___x_2845_ = lean_nat_add(v___x_2844_, v___x_2840_);
lean_dec(v___x_2844_);
v___x_2846_ = l_Lean_InductiveVal_numCtors(v_val_2829_);
lean_dec_ref(v_val_2829_);
v___x_2847_ = lean_nat_add(v___x_2845_, v___x_2846_);
lean_dec(v___x_2846_);
v___x_2848_ = lean_array_get_size(v_args_2842_);
v___x_2849_ = lean_nat_dec_le(v___x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2852_; 
lean_dec(v___x_2847_);
lean_dec(v___x_2845_);
lean_dec(v___x_2843_);
lean_dec_ref(v_args_2842_);
lean_dec(v_ctors_2836_);
lean_dec(v_numIndices_2835_);
lean_dec(v_numParams_2834_);
lean_dec_ref(v_toConstantVal_2833_);
lean_del_object(v___x_2831_);
lean_dec(v_us_2771_);
lean_dec(v_declName_2770_);
v___x_2850_ = lean_box(0);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2850_);
v___x_2852_ = v___x_2827_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
else
{
lean_object* v___x_2854_; lean_object* v_params_2855_; lean_object* v___x_2856_; lean_object* v_motive_2857_; lean_object* v_discrs_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_discrInfos_2861_; lean_object* v_alts_2862_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v_lower_2904_; lean_object* v_upper_2905_; uint8_t v___x_2912_; 
lean_del_object(v___x_2827_);
v___x_2854_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2834_);
lean_inc_ref(v_args_2842_);
v_params_2855_ = l_Array_toSubarray___redArg(v_args_2842_, v___x_2854_, v_numParams_2834_);
v___x_2856_ = l_Lean_instInhabitedExpr;
v_motive_2857_ = lean_array_get(v___x_2856_, v_args_2842_, v_numParams_2834_);
lean_dec(v_numParams_2834_);
lean_inc(v___x_2845_);
lean_inc_ref(v_args_2842_);
v_discrs_2858_ = l_Array_toSubarray___redArg(v_args_2842_, v___x_2843_, v___x_2845_);
v___x_2859_ = lean_nat_add(v_numIndices_2835_, v___x_2840_);
lean_dec(v_numIndices_2835_);
v___x_2860_ = lean_box(0);
v_discrInfos_2861_ = lean_mk_array(v___x_2859_, v___x_2860_);
lean_inc(v___x_2847_);
lean_inc_ref(v_args_2842_);
v_alts_2862_ = l_Array_toSubarray___redArg(v_args_2842_, v___x_2845_, v___x_2847_);
v___x_2912_ = lean_nat_dec_le(v___x_2847_, v___x_2854_);
if (v___x_2912_ == 0)
{
v_lower_2904_ = v___x_2847_;
v_upper_2905_ = v___x_2848_;
goto v___jp_2903_;
}
else
{
lean_dec(v___x_2847_);
v_lower_2904_ = v___x_2854_;
v_upper_2905_ = v___x_2848_;
goto v___jp_2903_;
}
v___jp_2863_:
{
lean_object* v___x_2866_; size_t v_sz_2867_; size_t v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = lean_array_mk(v_ctors_2836_);
v_sz_2867_ = lean_array_size(v___x_2866_);
v___x_2868_ = ((size_t)0ULL);
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2867_, v___x_2868_, v___x_2866_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2894_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2894_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2894_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_start_2874_; lean_object* v_stop_2875_; lean_object* v_start_2876_; lean_object* v_stop_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v_start_2874_ = lean_ctor_get(v_params_2855_, 1);
lean_inc(v_start_2874_);
v_stop_2875_ = lean_ctor_get(v_params_2855_, 2);
lean_inc(v_stop_2875_);
v_start_2876_ = lean_ctor_get(v_discrs_2858_, 1);
lean_inc(v_start_2876_);
v_stop_2877_ = lean_ctor_get(v_discrs_2858_, 2);
lean_inc(v_stop_2877_);
v___x_2878_ = lean_nat_sub(v_stop_2875_, v_start_2874_);
lean_dec(v_start_2874_);
lean_dec(v_stop_2875_);
v___x_2879_ = lean_nat_sub(v_stop_2877_, v_start_2876_);
lean_dec(v_start_2876_);
lean_dec(v_stop_2877_);
v___x_2880_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2881_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
lean_ctor_set(v___x_2881_, 1, v___x_2879_);
lean_ctor_set(v___x_2881_, 2, v_a_2870_);
lean_ctor_set(v___x_2881_, 3, v___y_2865_);
lean_ctor_set(v___x_2881_, 4, v_discrInfos_2861_);
lean_ctor_set(v___x_2881_, 5, v___x_2880_);
v___x_2882_ = lean_array_mk(v_us_2771_);
v___x_2883_ = l_Subarray_copy___redArg(v_params_2855_);
v___x_2884_ = l_Subarray_copy___redArg(v_discrs_2858_);
v___x_2885_ = l_Subarray_copy___redArg(v_alts_2862_);
v___x_2886_ = l_Subarray_copy___redArg(v___y_2864_);
v___x_2887_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2881_);
lean_ctor_set(v___x_2887_, 1, v_declName_2770_);
lean_ctor_set(v___x_2887_, 2, v___x_2882_);
lean_ctor_set(v___x_2887_, 3, v___x_2883_);
lean_ctor_set(v___x_2887_, 4, v_motive_2857_);
lean_ctor_set(v___x_2887_, 5, v___x_2884_);
lean_ctor_set(v___x_2887_, 6, v___x_2885_);
lean_ctor_set(v___x_2887_, 7, v___x_2886_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set_tag(v___x_2831_, 1);
lean_ctor_set(v___x_2831_, 0, v___x_2887_);
v___x_2889_ = v___x_2831_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2891_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2889_);
v___x_2891_ = v___x_2872_;
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
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_alts_2862_);
lean_dec_ref(v_discrInfos_2861_);
lean_dec_ref(v_discrs_2858_);
lean_dec(v_motive_2857_);
lean_dec_ref(v_params_2855_);
lean_del_object(v___x_2831_);
lean_dec(v_us_2771_);
lean_dec(v_declName_2770_);
v_a_2895_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2869_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2869_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
v___jp_2903_:
{
lean_object* v_levelParams_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v_levelParams_2906_ = lean_ctor_get(v_toConstantVal_2833_, 1);
lean_inc(v_levelParams_2906_);
lean_dec_ref(v_toConstantVal_2833_);
v___x_2907_ = l_Array_toSubarray___redArg(v_args_2842_, v_lower_2904_, v_upper_2905_);
v___x_2908_ = l_List_lengthTR___redArg(v_levelParams_2906_);
lean_dec(v_levelParams_2906_);
v___x_2909_ = l_List_lengthTR___redArg(v_us_2771_);
v___x_2910_ = lean_nat_dec_eq(v___x_2908_, v___x_2909_);
lean_dec(v___x_2909_);
lean_dec(v___x_2908_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2864_ = v___x_2907_;
v___y_2865_ = v___x_2911_;
goto v___jp_2863_;
}
else
{
v___y_2864_ = v___x_2907_;
v___y_2865_ = v___x_2860_;
goto v___jp_2863_;
}
}
}
}
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
lean_dec(v_a_2825_);
lean_dec(v_us_2771_);
lean_dec(v_declName_2770_);
lean_dec_ref(v_e_2755_);
v___x_2914_ = lean_box(0);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2914_);
v___x_2916_ = v___x_2827_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_us_2771_);
lean_dec(v_declName_2770_);
lean_dec_ref(v_e_2755_);
v_a_2919_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2824_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2824_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
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
lean_dec_ref(v___x_2769_);
lean_dec_ref(v_e_2755_);
goto v___jp_2763_;
}
}
v___jp_2763_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_box(0);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2928_, lean_object* v_alsoCasesOn_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2936_; lean_object* v_res_2937_; 
v_alsoCasesOn_boxed_2936_ = lean_unbox(v_alsoCasesOn_2929_);
v_res_2937_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2928_, v_alsoCasesOn_boxed_2936_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
if (lean_obj_tag(v_a_2938_) == 0)
{
lean_object* v___x_2940_; 
v___x_2940_ = l_List_reverse___redArg(v_a_2939_);
return v___x_2940_;
}
else
{
lean_object* v_head_2941_; lean_object* v_tail_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2951_; 
v_head_2941_ = lean_ctor_get(v_a_2938_, 0);
v_tail_2942_ = lean_ctor_get(v_a_2938_, 1);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2944_ = v_a_2938_;
v_isShared_2945_ = v_isSharedCheck_2951_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_tail_2942_);
lean_inc(v_head_2941_);
lean_dec(v_a_2938_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2951_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = l_Lean_MessageData_ofExpr(v_head_2941_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_a_2939_);
lean_ctor_set(v___x_2944_, 0, v___x_2946_);
v___x_2948_ = v___x_2944_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_a_2939_);
v___x_2948_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
v_a_2938_ = v_tail_2942_;
v_a_2939_ = v___x_2948_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2952_, lean_object* v_x_2953_){
_start:
{
lean_object* v_fnName_2954_; uint8_t v___x_2955_; 
v_fnName_2954_ = lean_ctor_get(v_x_2953_, 0);
v___x_2955_ = l_Lean_Expr_isConstOf(v_x_2952_, v_fnName_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
uint8_t v_res_2958_; lean_object* v_r_2959_; 
v_res_2958_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2956_, v_x_2957_);
lean_dec_ref(v_x_2957_);
lean_dec_ref(v_x_2956_);
v_r_2959_ = lean_box(v_res_2958_);
return v_r_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2960_, lean_object* v_type_2961_, lean_object* v_val_2962_, lean_object* v_k_2963_, uint8_t v_nondep_2964_, uint8_t v_kind_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___f_2972_; lean_object* v___x_2973_; 
lean_inc(v___y_2966_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2972_, 0, v_k_2963_);
lean_closure_set(v___f_2972_, 1, v___y_2966_);
v___x_2973_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2960_, v_type_2961_, v_val_2962_, v___f_2972_, v_nondep_2964_, v_kind_2965_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2973_) == 0)
{
return v___x_2973_;
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2982_, lean_object* v_type_2983_, lean_object* v_val_2984_, lean_object* v_k_2985_, lean_object* v_nondep_2986_, lean_object* v_kind_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v_nondep_boxed_2994_; uint8_t v_kind_boxed_2995_; lean_object* v_res_2996_; 
v_nondep_boxed_2994_ = lean_unbox(v_nondep_2986_);
v_kind_boxed_2995_ = lean_unbox(v_kind_2987_);
v_res_2996_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2982_, v_type_2983_, v_val_2984_, v_k_2985_, v_nondep_boxed_2994_, v_kind_boxed_2995_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2997_, uint8_t v_usedLetOnly_2998_, lean_object* v_x_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; 
lean_inc(v___y_3004_);
lean_inc_ref(v___y_3003_);
lean_inc(v___y_3002_);
lean_inc_ref(v___y_3001_);
lean_inc(v___y_3000_);
lean_inc_ref(v_x_2999_);
v___x_3006_ = lean_apply_7(v_k_2997_, v_x_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, lean_box(0));
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
v___x_3008_ = lean_unsigned_to_nat(1u);
v___x_3009_ = lean_mk_empty_array_with_capacity(v___x_3008_);
v___x_3010_ = lean_array_push(v___x_3009_, v_x_2999_);
v___x_3011_ = 0;
v___x_3012_ = 1;
v___x_3013_ = l_Lean_Meta_mkLetFVars(v___x_3010_, v_a_3007_, v_usedLetOnly_2998_, v___x_3011_, v___x_3012_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec_ref(v___x_3010_);
return v___x_3013_;
}
else
{
lean_dec_ref(v_x_2999_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_3014_, lean_object* v_usedLetOnly_3015_, lean_object* v_x_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
uint8_t v_usedLetOnly_boxed_3023_; lean_object* v_res_3024_; 
v_usedLetOnly_boxed_3023_ = lean_unbox(v_usedLetOnly_3015_);
v_res_3024_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_3014_, v_usedLetOnly_boxed_3023_, v_x_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_3025_, lean_object* v_type_3026_, lean_object* v_val_3027_, lean_object* v_k_3028_, uint8_t v_nondep_3029_, uint8_t v_kind_3030_, uint8_t v_usedLetOnly_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v___f_3039_; lean_object* v___x_3040_; 
v___x_3038_ = lean_box(v_usedLetOnly_3031_);
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3039_, 0, v_k_3028_);
lean_closure_set(v___f_3039_, 1, v___x_3038_);
v___x_3040_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3025_, v_type_3026_, v_val_3027_, v___f_3039_, v_nondep_3029_, v_kind_3030_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_3041_, lean_object* v_type_3042_, lean_object* v_val_3043_, lean_object* v_k_3044_, lean_object* v_nondep_3045_, lean_object* v_kind_3046_, lean_object* v_usedLetOnly_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
uint8_t v_nondep_boxed_3054_; uint8_t v_kind_boxed_3055_; uint8_t v_usedLetOnly_boxed_3056_; lean_object* v_res_3057_; 
v_nondep_boxed_3054_ = lean_unbox(v_nondep_3045_);
v_kind_boxed_3055_ = lean_unbox(v_kind_3046_);
v_usedLetOnly_boxed_3056_ = lean_unbox(v_usedLetOnly_3047_);
v_res_3057_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_3041_, v_type_3042_, v_val_3043_, v_k_3044_, v_nondep_boxed_3054_, v_kind_boxed_3055_, v_usedLetOnly_boxed_3056_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_3058_, lean_object* v_positions_3059_, lean_object* v_recFnNames_3060_, lean_object* v_containsRecFn_3061_, lean_object* v_below_3062_, size_t v_sz_3063_, size_t v_i_3064_, lean_object* v_bs_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
uint8_t v___x_3072_; 
v___x_3072_ = lean_usize_dec_lt(v_i_3064_, v_sz_3063_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; 
lean_dec_ref(v_below_3062_);
lean_dec_ref(v_containsRecFn_3061_);
lean_dec_ref(v_recFnNames_3060_);
lean_dec_ref(v_positions_3059_);
lean_dec_ref(v_recArgInfos_3058_);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v_bs_3065_);
return v___x_3073_;
}
else
{
lean_object* v_v_3074_; lean_object* v___x_3075_; 
v_v_3074_ = lean_array_uget_borrowed(v_bs_3065_, v_i_3064_);
lean_inc_ref(v___y_3069_);
lean_inc(v_v_3074_);
lean_inc_ref(v_below_3062_);
lean_inc_ref(v_containsRecFn_3061_);
lean_inc_ref(v_recFnNames_3060_);
lean_inc_ref(v_positions_3059_);
lean_inc_ref(v_recArgInfos_3058_);
v___x_3075_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3058_, v_positions_3059_, v_recFnNames_3060_, v_containsRecFn_3061_, v_below_3062_, v_v_3074_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3077_; lean_object* v_bs_x27_3078_; size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref(v___x_3075_);
v___x_3077_ = lean_unsigned_to_nat(0u);
v_bs_x27_3078_ = lean_array_uset(v_bs_3065_, v_i_3064_, v___x_3077_);
v___x_3079_ = ((size_t)1ULL);
v___x_3080_ = lean_usize_add(v_i_3064_, v___x_3079_);
v___x_3081_ = lean_array_uset(v_bs_x27_3078_, v_i_3064_, v_a_3076_);
v_i_3064_ = v___x_3080_;
v_bs_3065_ = v___x_3081_;
goto _start;
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec_ref(v_bs_3065_);
lean_dec_ref(v_below_3062_);
lean_dec_ref(v_containsRecFn_3061_);
lean_dec_ref(v_recFnNames_3060_);
lean_dec_ref(v_positions_3059_);
lean_dec_ref(v_recArgInfos_3058_);
v_a_3083_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3075_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3075_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3093_ = l_Lean_stringToMessageData(v___x_3092_);
return v___x_3093_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3096_ = l_Lean_stringToMessageData(v___x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3097_, lean_object* v_positions_3098_, lean_object* v_recFnNames_3099_, lean_object* v_containsRecFn_3100_, lean_object* v_below_3101_, lean_object* v_e_3102_, lean_object* v_x_3103_, lean_object* v_x_3104_, lean_object* v_x_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
if (lean_obj_tag(v_x_3103_) == 5)
{
lean_object* v_fn_3112_; lean_object* v_arg_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_fn_3112_ = lean_ctor_get(v_x_3103_, 0);
lean_inc_ref(v_fn_3112_);
v_arg_3113_ = lean_ctor_get(v_x_3103_, 1);
lean_inc_ref(v_arg_3113_);
lean_dec_ref(v_x_3103_);
v___x_3114_ = lean_array_set(v_x_3104_, v_x_3105_, v_arg_3113_);
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_nat_sub(v_x_3105_, v___x_3115_);
lean_dec(v_x_3105_);
v_x_3103_ = v_fn_3112_;
v_x_3104_ = v___x_3114_;
v_x_3105_ = v___x_3116_;
goto _start;
}
else
{
lean_object* v___f_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec(v_x_3105_);
lean_inc_ref(v_x_3103_);
v___f_3118_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3118_, 0, v_x_3103_);
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3118_, v_recArgInfos_3097_, v___x_3119_);
if (lean_obj_tag(v___x_3120_) == 1)
{
lean_object* v_val_3121_; lean_object* v___x_3122_; lean_object* v___y_3124_; lean_object* v_recArgPos_3150_; lean_object* v_indGroupInst_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
lean_dec_ref(v_x_3103_);
v_val_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_val_3121_);
lean_dec_ref(v___x_3120_);
v___x_3122_ = lean_array_fget_borrowed(v_recArgInfos_3097_, v_val_3121_);
v_recArgPos_3150_ = lean_ctor_get(v___x_3122_, 2);
v_indGroupInst_3151_ = lean_ctor_get(v___x_3122_, 4);
v___x_3152_ = lean_array_get_size(v_x_3104_);
v___x_3153_ = lean_nat_dec_lt(v_recArgPos_3150_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec(v_val_3121_);
lean_dec_ref(v_x_3104_);
lean_dec_ref(v_below_3101_);
lean_dec_ref(v_containsRecFn_3100_);
lean_dec_ref(v_recFnNames_3099_);
lean_dec_ref(v_positions_3098_);
lean_dec_ref(v_recArgInfos_3097_);
v___x_3154_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3155_ = l_Lean_indentExpr(v_e_3102_);
v___x_3156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3154_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3156_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
return v___x_3157_;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_array_fget_borrowed(v_x_3104_, v_recArgPos_3150_);
lean_inc_ref(v___y_3109_);
lean_inc(v___x_3158_);
lean_inc_ref(v_below_3101_);
lean_inc_ref(v_containsRecFn_3100_);
lean_inc_ref(v_recFnNames_3099_);
lean_inc_ref(v_positions_3098_);
lean_inc_ref(v_recArgInfos_3097_);
v___x_3159_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3097_, v_positions_3098_, v_recFnNames_3099_, v_containsRecFn_3100_, v_below_3101_, v___x_3158_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v_params_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v_params_3161_ = lean_ctor_get(v_indGroupInst_3151_, 2);
v___x_3162_ = lean_array_get_size(v_params_3161_);
lean_inc_ref(v_positions_3098_);
lean_inc_ref(v_below_3101_);
v___x_3163_ = l_Lean_Elab_Structural_toBelow(v_below_3101_, v___x_3162_, v_positions_3098_, v_val_3121_, v_a_3160_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_dec_ref(v_e_3102_);
v___y_3124_ = v___x_3163_;
goto v___jp_3123_;
}
else
{
lean_object* v_a_3164_; uint8_t v___y_3166_; uint8_t v___x_3171_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
v___x_3171_ = l_Lean_Exception_isInterrupt(v_a_3164_);
if (v___x_3171_ == 0)
{
uint8_t v___x_3172_; 
v___x_3172_ = l_Lean_Exception_isRuntime(v_a_3164_);
v___y_3166_ = v___x_3172_;
goto v___jp_3165_;
}
else
{
lean_dec(v_a_3164_);
v___y_3166_ = v___x_3171_;
goto v___jp_3165_;
}
v___jp_3165_:
{
if (v___y_3166_ == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_dec_ref(v___x_3163_);
v___x_3167_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3168_ = l_Lean_indentExpr(v_e_3102_);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3169_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
v___y_3124_ = v___x_3170_;
goto v___jp_3123_;
}
else
{
lean_dec_ref(v_e_3102_);
v___y_3124_ = v___x_3163_;
goto v___jp_3123_;
}
}
}
}
else
{
lean_dec(v_val_3121_);
lean_dec_ref(v_x_3104_);
lean_dec_ref(v_e_3102_);
lean_dec_ref(v_below_3101_);
lean_dec_ref(v_containsRecFn_3100_);
lean_dec_ref(v_recFnNames_3099_);
lean_dec_ref(v_positions_3098_);
lean_dec_ref(v_recArgInfos_3097_);
return v___x_3159_;
}
}
v___jp_3123_:
{
if (lean_obj_tag(v___y_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v_fixedParamPerm_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v_snd_3129_; size_t v_sz_3130_; size_t v___x_3131_; lean_object* v___x_3132_; 
v_a_3125_ = lean_ctor_get(v___y_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref(v___y_3124_);
v_fixedParamPerm_3126_ = lean_ctor_get(v___x_3122_, 1);
v___x_3127_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3126_, v_x_3104_);
lean_dec_ref(v_x_3104_);
lean_inc(v___x_3122_);
v___x_3128_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3122_, v___x_3127_);
v_snd_3129_ = lean_ctor_get(v___x_3128_, 1);
lean_inc(v_snd_3129_);
lean_dec_ref(v___x_3128_);
v_sz_3130_ = lean_array_size(v_snd_3129_);
v___x_3131_ = ((size_t)0ULL);
v___x_3132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3097_, v_positions_3098_, v_recFnNames_3099_, v_containsRecFn_3100_, v_below_3101_, v_sz_3130_, v___x_3131_, v_snd_3129_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3141_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3141_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3141_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3137_ = l_Lean_mkAppN(v_a_3125_, v_a_3133_);
lean_dec(v_a_3133_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3139_ = v___x_3135_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_a_3125_);
v_a_3142_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3132_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3132_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_dec_ref(v_x_3104_);
lean_dec_ref(v_below_3101_);
lean_dec_ref(v_containsRecFn_3100_);
lean_dec_ref(v_recFnNames_3099_);
lean_dec_ref(v_positions_3098_);
lean_dec_ref(v_recArgInfos_3097_);
return v___y_3124_;
}
}
}
else
{
lean_object* v___x_3173_; 
lean_dec(v___x_3120_);
lean_dec_ref(v_e_3102_);
lean_inc_ref(v___y_3109_);
lean_inc_ref(v_below_3101_);
lean_inc_ref(v_containsRecFn_3100_);
lean_inc_ref(v_recFnNames_3099_);
lean_inc_ref(v_positions_3098_);
lean_inc_ref(v_recArgInfos_3097_);
v___x_3173_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3097_, v_positions_3098_, v_recFnNames_3099_, v_containsRecFn_3100_, v_below_3101_, v_x_3103_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; size_t v_sz_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref(v___x_3173_);
v_sz_3175_ = lean_array_size(v_x_3104_);
v___x_3176_ = ((size_t)0ULL);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3097_, v_positions_3098_, v_recFnNames_3099_, v_containsRecFn_3100_, v_below_3101_, v_sz_3175_, v___x_3176_, v_x_3104_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3186_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3182_ = l_Lean_mkAppN(v_a_3174_, v_a_3178_);
lean_dec(v_a_3178_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3182_);
v___x_3184_ = v___x_3180_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_a_3174_);
v_a_3187_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3177_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3177_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_dec_ref(v_x_3104_);
lean_dec_ref(v_below_3101_);
lean_dec_ref(v_containsRecFn_3100_);
lean_dec_ref(v_recFnNames_3099_);
lean_dec_ref(v_positions_3098_);
lean_dec_ref(v_recArgInfos_3097_);
return v___x_3173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3195_, lean_object* v_recArgInfos_3196_, lean_object* v_positions_3197_, lean_object* v_recFnNames_3198_, lean_object* v_containsRecFn_3199_, lean_object* v_below_3200_, uint8_t v___x_3201_, uint8_t v_a_3202_, lean_object* v_x_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
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
lean_dec_ref(v___x_3211_);
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_mk_empty_array_with_capacity(v___x_3213_);
v___x_3215_ = lean_array_push(v___x_3214_, v_x_3203_);
v___x_3216_ = 1;
v___x_3217_ = l_Lean_Meta_mkLambdaFVars(v___x_3215_, v_a_3212_, v___x_3201_, v_a_3202_, v___x_3201_, v_a_3202_, v___x_3216_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3218_, lean_object* v_recArgInfos_3219_, lean_object* v_positions_3220_, lean_object* v_recFnNames_3221_, lean_object* v_containsRecFn_3222_, lean_object* v_below_3223_, lean_object* v___x_3224_, lean_object* v_a_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
uint8_t v___x_31257__boxed_3233_; uint8_t v_a_31258__boxed_3234_; lean_object* v_res_3235_; 
v___x_31257__boxed_3233_ = lean_unbox(v___x_3224_);
v_a_31258__boxed_3234_ = lean_unbox(v_a_3225_);
v_res_3235_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3218_, v_recArgInfos_3219_, v_positions_3220_, v_recFnNames_3221_, v_containsRecFn_3222_, v_below_3223_, v___x_31257__boxed_3233_, v_a_31258__boxed_3234_, v_x_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v_body_3218_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3236_, lean_object* v_recArgInfos_3237_, lean_object* v_positions_3238_, lean_object* v_recFnNames_3239_, lean_object* v_containsRecFn_3240_, lean_object* v_below_3241_, uint8_t v___x_3242_, uint8_t v_a_3243_, lean_object* v_x_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = lean_expr_instantiate1(v_body_3236_, v_x_3244_);
lean_inc_ref(v___y_3248_);
v___x_3252_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3237_, v_positions_3238_, v_recFnNames_3239_, v_containsRecFn_3240_, v_below_3241_, v___x_3251_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3252_);
v___x_3254_ = lean_unsigned_to_nat(1u);
v___x_3255_ = lean_mk_empty_array_with_capacity(v___x_3254_);
v___x_3256_ = lean_array_push(v___x_3255_, v_x_3244_);
v___x_3257_ = 1;
v___x_3258_ = l_Lean_Meta_mkForallFVars(v___x_3256_, v_a_3253_, v___x_3242_, v_a_3243_, v_a_3243_, v___x_3257_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec_ref(v___x_3256_);
return v___x_3258_;
}
else
{
lean_dec_ref(v_x_3244_);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3259_, lean_object* v_recArgInfos_3260_, lean_object* v_positions_3261_, lean_object* v_recFnNames_3262_, lean_object* v_containsRecFn_3263_, lean_object* v_below_3264_, lean_object* v___x_3265_, lean_object* v_a_3266_, lean_object* v_x_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v___x_31275__boxed_3274_; uint8_t v_a_31276__boxed_3275_; lean_object* v_res_3276_; 
v___x_31275__boxed_3274_ = lean_unbox(v___x_3265_);
v_a_31276__boxed_3275_ = lean_unbox(v_a_3266_);
v_res_3276_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3259_, v_recArgInfos_3260_, v_positions_3261_, v_recFnNames_3262_, v_containsRecFn_3263_, v_below_3264_, v___x_31275__boxed_3274_, v_a_31276__boxed_3275_, v_x_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v_body_3259_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3277_, lean_object* v_recArgInfos_3278_, lean_object* v_positions_3279_, lean_object* v_recFnNames_3280_, lean_object* v_containsRecFn_3281_, lean_object* v_below_3282_, lean_object* v_x_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3277_, v_recArgInfos_3278_, v_positions_3279_, v_recFnNames_3280_, v_containsRecFn_3281_, v_below_3282_, v_x_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v_x_3283_);
lean_dec_ref(v_body_3277_);
return v_res_3290_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__0));
v___x_3295_ = l_Lean_stringToMessageData(v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__2));
v___x_3298_ = l_Lean_stringToMessageData(v___x_3297_);
return v___x_3298_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__4));
v___x_3301_ = l_Lean_stringToMessageData(v___x_3300_);
return v___x_3301_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__6));
v___x_3304_ = l_Lean_stringToMessageData(v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0(lean_object* v___x_3305_, lean_object* v_b_3306_, lean_object* v_recArgInfos_3307_, lean_object* v_positions_3308_, lean_object* v_recFnNames_3309_, lean_object* v_containsRecFn_3310_, uint8_t v___x_3311_, uint8_t v_a_3312_, lean_object* v___x_3313_, lean_object* v_a_3314_, lean_object* v_e_3315_, lean_object* v_xs_3316_, lean_object* v_altBody_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___x_3360_; lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3389_; 
lean_inc(v___x_3305_);
v___x_3360_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v___x_3305_, v___y_3321_);
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3389_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3389_;
goto v_resetjp_3362_;
}
v___jp_3324_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = l_Lean_instInhabitedExpr;
v___x_3331_ = lean_array_get_borrowed(v___x_3330_, v_xs_3316_, v_b_3306_);
lean_dec(v_b_3306_);
lean_inc_ref(v___y_3328_);
lean_inc(v___x_3331_);
v___x_3332_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3307_, v_positions_3308_, v_recFnNames_3309_, v_containsRecFn_3310_, v___x_3331_, v_altBody_3317_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; uint8_t v___x_3334_; lean_object* v___x_3335_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = 1;
v___x_3335_ = l_Lean_Meta_mkLambdaFVars(v_xs_3316_, v_a_3333_, v___x_3311_, v_a_3312_, v___x_3311_, v_a_3312_, v___x_3334_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec_ref(v_xs_3316_);
return v___x_3335_;
}
else
{
lean_dec_ref(v_xs_3316_);
return v___x_3332_;
}
}
v___jp_3336_:
{
lean_object* v___x_3342_; uint8_t v___x_3343_; 
v___x_3342_ = lean_array_get_size(v_xs_3316_);
v___x_3343_ = lean_nat_dec_eq(v___x_3342_, v___x_3313_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec_ref(v_altBody_3317_);
lean_dec_ref(v_xs_3316_);
lean_dec_ref(v_containsRecFn_3310_);
lean_dec_ref(v_recFnNames_3309_);
lean_dec_ref(v_positions_3308_);
lean_dec_ref(v_recArgInfos_3307_);
lean_dec(v_b_3306_);
v___x_3344_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__1);
v___x_3345_ = l_Lean_indentExpr(v_a_3314_);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3344_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__3);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = l_Lean_indentExpr(v_e_3315_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3350_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
else
{
lean_dec_ref(v_e_3315_);
lean_dec_ref(v_a_3314_);
v___y_3325_ = v___y_3337_;
v___y_3326_ = v___y_3338_;
v___y_3327_ = v___y_3339_;
v___y_3328_ = v___y_3340_;
v___y_3329_ = v___y_3341_;
goto v___jp_3324_;
}
}
v_resetjp_3362_:
{
uint8_t v___x_3365_; 
v___x_3365_ = lean_unbox(v_a_3361_);
lean_dec(v_a_3361_);
if (v___x_3365_ == 0)
{
lean_del_object(v___x_3363_);
lean_dec(v___x_3305_);
v___y_3337_ = v___y_3318_;
v___y_3338_ = v___y_3319_;
v___y_3339_ = v___y_3320_;
v___y_3340_ = v___y_3321_;
v___y_3341_ = v___y_3322_;
goto v___jp_3336_;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3366_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__5);
lean_inc(v_b_3306_);
v___x_3367_ = l_Nat_reprFast(v_b_3306_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set_tag(v___x_3363_, 3);
lean_ctor_set(v___x_3363_, 0, v___x_3367_);
v___x_3369_ = v___x_3363_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3370_ = l_Lean_MessageData_ofFormat(v___x_3369_);
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3366_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___closed__7);
v___x_3373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
lean_inc_ref(v_xs_3316_);
v___x_3374_ = lean_array_to_list(v_xs_3316_);
v___x_3375_ = lean_box(0);
v___x_3376_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v___x_3374_, v___x_3375_);
v___x_3377_ = l_Lean_MessageData_ofList(v___x_3376_);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3373_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v___x_3305_, v___x_3378_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_dec_ref(v___x_3379_);
v___y_3337_ = v___y_3318_;
v___y_3338_ = v___y_3319_;
v___y_3339_ = v___y_3320_;
v___y_3340_ = v___y_3321_;
v___y_3341_ = v___y_3322_;
goto v___jp_3336_;
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref(v_altBody_3317_);
lean_dec_ref(v_xs_3316_);
lean_dec_ref(v_e_3315_);
lean_dec_ref(v_a_3314_);
lean_dec_ref(v_containsRecFn_3310_);
lean_dec_ref(v_recFnNames_3309_);
lean_dec_ref(v_positions_3308_);
lean_dec_ref(v_recArgInfos_3307_);
lean_dec(v_b_3306_);
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___boxed(lean_object** _args){
lean_object* v___x_3390_ = _args[0];
lean_object* v_b_3391_ = _args[1];
lean_object* v_recArgInfos_3392_ = _args[2];
lean_object* v_positions_3393_ = _args[3];
lean_object* v_recFnNames_3394_ = _args[4];
lean_object* v_containsRecFn_3395_ = _args[5];
lean_object* v___x_3396_ = _args[6];
lean_object* v_a_3397_ = _args[7];
lean_object* v___x_3398_ = _args[8];
lean_object* v_a_3399_ = _args[9];
lean_object* v_e_3400_ = _args[10];
lean_object* v_xs_3401_ = _args[11];
lean_object* v_altBody_3402_ = _args[12];
lean_object* v___y_3403_ = _args[13];
lean_object* v___y_3404_ = _args[14];
lean_object* v___y_3405_ = _args[15];
lean_object* v___y_3406_ = _args[16];
lean_object* v___y_3407_ = _args[17];
lean_object* v___y_3408_ = _args[18];
_start:
{
uint8_t v___x_31350__boxed_3409_; uint8_t v_a_31351__boxed_3410_; lean_object* v_res_3411_; 
v___x_31350__boxed_3409_ = lean_unbox(v___x_3396_);
v_a_31351__boxed_3410_ = lean_unbox(v_a_3397_);
v_res_3411_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0(v___x_3390_, v_b_3391_, v_recArgInfos_3392_, v_positions_3393_, v_recFnNames_3394_, v_containsRecFn_3395_, v___x_31350__boxed_3409_, v_a_31351__boxed_3410_, v___x_3398_, v_a_3399_, v_e_3400_, v_xs_3401_, v_altBody_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec(v___x_3398_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11(lean_object* v_recArgInfos_3412_, lean_object* v_positions_3413_, lean_object* v_recFnNames_3414_, lean_object* v_containsRecFn_3415_, uint8_t v_a_3416_, lean_object* v_e_3417_, lean_object* v_as_3418_, lean_object* v_bs_3419_, lean_object* v_i_3420_, lean_object* v_cs_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3428_ = lean_array_get_size(v_as_3418_);
v___x_3429_ = lean_nat_dec_lt(v_i_3420_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec(v_i_3420_);
lean_dec_ref(v_e_3417_);
lean_dec_ref(v_containsRecFn_3415_);
lean_dec_ref(v_recFnNames_3414_);
lean_dec_ref(v_positions_3413_);
lean_dec_ref(v_recArgInfos_3412_);
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v_cs_3421_);
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3431_ = lean_array_get_size(v_bs_3419_);
v___x_3432_ = lean_nat_dec_lt(v_i_3420_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; 
lean_dec(v_i_3420_);
lean_dec_ref(v_e_3417_);
lean_dec_ref(v_containsRecFn_3415_);
lean_dec_ref(v_recFnNames_3414_);
lean_dec_ref(v_positions_3413_);
lean_dec_ref(v_recArgInfos_3412_);
v___x_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_cs_3421_);
return v___x_3433_;
}
else
{
uint8_t v___x_3434_; lean_object* v___x_3435_; lean_object* v_a_3436_; lean_object* v_b_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___f_3442_; lean_object* v___x_3443_; 
v___x_3434_ = 0;
v___x_3435_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3436_ = lean_array_fget_borrowed(v_as_3418_, v_i_3420_);
v_b_3437_ = lean_array_fget_borrowed(v_bs_3419_, v_i_3420_);
v___x_3438_ = lean_unsigned_to_nat(1u);
v___x_3439_ = lean_nat_add(v_b_3437_, v___x_3438_);
v___x_3440_ = lean_box(v___x_3434_);
v___x_3441_ = lean_box(v_a_3416_);
lean_inc_ref(v_e_3417_);
lean_inc(v_a_3436_);
lean_inc(v___x_3439_);
lean_inc_ref(v_containsRecFn_3415_);
lean_inc_ref(v_recFnNames_3414_);
lean_inc_ref(v_positions_3413_);
lean_inc_ref(v_recArgInfos_3412_);
lean_inc(v_b_3437_);
v___f_3442_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___lam__0___boxed), 19, 11);
lean_closure_set(v___f_3442_, 0, v___x_3435_);
lean_closure_set(v___f_3442_, 1, v_b_3437_);
lean_closure_set(v___f_3442_, 2, v_recArgInfos_3412_);
lean_closure_set(v___f_3442_, 3, v_positions_3413_);
lean_closure_set(v___f_3442_, 4, v_recFnNames_3414_);
lean_closure_set(v___f_3442_, 5, v_containsRecFn_3415_);
lean_closure_set(v___f_3442_, 6, v___x_3440_);
lean_closure_set(v___f_3442_, 7, v___x_3441_);
lean_closure_set(v___f_3442_, 8, v___x_3439_);
lean_closure_set(v___f_3442_, 9, v_a_3436_);
lean_closure_set(v___f_3442_, 10, v_e_3417_);
lean_inc(v_a_3436_);
v___x_3443_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___redArg(v_a_3436_, v___x_3439_, v___f_3442_, v___x_3434_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref(v___x_3443_);
v___x_3445_ = lean_nat_add(v_i_3420_, v___x_3438_);
lean_dec(v_i_3420_);
v___x_3446_ = lean_array_push(v_cs_3421_, v_a_3444_);
v_i_3420_ = v___x_3445_;
v_cs_3421_ = v___x_3446_;
goto _start;
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec_ref(v_cs_3421_);
lean_dec(v_i_3420_);
lean_dec_ref(v_e_3417_);
lean_dec_ref(v_containsRecFn_3415_);
lean_dec_ref(v_recFnNames_3414_);
lean_dec_ref(v_positions_3413_);
lean_dec_ref(v_recArgInfos_3412_);
v_a_3448_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3443_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3443_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
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
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3458_ = l_Lean_stringToMessageData(v___x_3457_);
return v___x_3458_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3461_ = l_Lean_stringToMessageData(v___x_3460_);
return v___x_3461_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3464_ = l_Lean_stringToMessageData(v___x_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3465_, lean_object* v_positions_3466_, lean_object* v_recFnNames_3467_, lean_object* v_containsRecFn_3468_, lean_object* v_below_3469_, lean_object* v_e_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v_e_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___x_3490_; 
lean_inc_ref(v_containsRecFn_3468_);
lean_inc(v_a_3475_);
lean_inc_ref(v_a_3474_);
lean_inc(v_a_3473_);
lean_inc_ref(v_a_3472_);
lean_inc(v_a_3471_);
lean_inc_ref(v_e_3470_);
v___x_3490_ = lean_apply_7(v_containsRecFn_3468_, v_e_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, lean_box(0));
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3711_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3711_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3711_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
uint8_t v___x_3495_; 
v___x_3495_ = lean_unbox(v_a_3491_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3497_; 
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_e_3470_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_e_3470_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
else
{
uint8_t v___x_3499_; 
lean_del_object(v___x_3493_);
v___x_3499_ = 0;
switch(lean_obj_tag(v_e_3470_))
{
case 6:
{
lean_object* v_binderName_3500_; lean_object* v_binderType_3501_; lean_object* v_body_3502_; uint8_t v_binderInfo_3503_; lean_object* v___x_3504_; 
v_binderName_3500_ = lean_ctor_get(v_e_3470_, 0);
lean_inc(v_binderName_3500_);
v_binderType_3501_ = lean_ctor_get(v_e_3470_, 1);
lean_inc_ref(v_binderType_3501_);
v_body_3502_ = lean_ctor_get(v_e_3470_, 2);
lean_inc_ref(v_body_3502_);
v_binderInfo_3503_ = lean_ctor_get_uint8(v_e_3470_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3470_);
lean_inc_ref(v_a_3474_);
lean_inc_ref(v_below_3469_);
lean_inc_ref(v_containsRecFn_3468_);
lean_inc_ref(v_recFnNames_3467_);
lean_inc_ref(v_positions_3466_);
lean_inc_ref(v_recArgInfos_3465_);
v___x_3504_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3465_, v_positions_3466_, v_recFnNames_3467_, v_containsRecFn_3468_, v_below_3469_, v_binderType_3501_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3506_; lean_object* v___f_3507_; uint8_t v___x_3508_; lean_object* v___x_3509_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref(v___x_3504_);
v___x_3506_ = lean_box(v___x_3499_);
v___f_3507_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3507_, 0, v_body_3502_);
lean_closure_set(v___f_3507_, 1, v_recArgInfos_3465_);
lean_closure_set(v___f_3507_, 2, v_positions_3466_);
lean_closure_set(v___f_3507_, 3, v_recFnNames_3467_);
lean_closure_set(v___f_3507_, 4, v_containsRecFn_3468_);
lean_closure_set(v___f_3507_, 5, v_below_3469_);
lean_closure_set(v___f_3507_, 6, v___x_3506_);
lean_closure_set(v___f_3507_, 7, v_a_3491_);
v___x_3508_ = 0;
v___x_3509_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3500_, v_binderInfo_3503_, v_a_3505_, v___f_3507_, v___x_3508_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec_ref(v_a_3474_);
return v___x_3509_;
}
else
{
lean_dec_ref(v_body_3502_);
lean_dec(v_binderName_3500_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
return v___x_3504_;
}
}
case 7:
{
lean_object* v_binderName_3510_; lean_object* v_binderType_3511_; lean_object* v_body_3512_; uint8_t v_binderInfo_3513_; lean_object* v___x_3514_; 
v_binderName_3510_ = lean_ctor_get(v_e_3470_, 0);
lean_inc(v_binderName_3510_);
v_binderType_3511_ = lean_ctor_get(v_e_3470_, 1);
lean_inc_ref(v_binderType_3511_);
v_body_3512_ = lean_ctor_get(v_e_3470_, 2);
lean_inc_ref(v_body_3512_);
v_binderInfo_3513_ = lean_ctor_get_uint8(v_e_3470_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3470_);
lean_inc_ref(v_a_3474_);
lean_inc_ref(v_below_3469_);
lean_inc_ref(v_containsRecFn_3468_);
lean_inc_ref(v_recFnNames_3467_);
lean_inc_ref(v_positions_3466_);
lean_inc_ref(v_recArgInfos_3465_);
v___x_3514_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3465_, v_positions_3466_, v_recFnNames_3467_, v_containsRecFn_3468_, v_below_3469_, v_binderType_3511_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; lean_object* v___f_3517_; uint8_t v___x_3518_; lean_object* v___x_3519_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref(v___x_3514_);
v___x_3516_ = lean_box(v___x_3499_);
v___f_3517_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3517_, 0, v_body_3512_);
lean_closure_set(v___f_3517_, 1, v_recArgInfos_3465_);
lean_closure_set(v___f_3517_, 2, v_positions_3466_);
lean_closure_set(v___f_3517_, 3, v_recFnNames_3467_);
lean_closure_set(v___f_3517_, 4, v_containsRecFn_3468_);
lean_closure_set(v___f_3517_, 5, v_below_3469_);
lean_closure_set(v___f_3517_, 6, v___x_3516_);
lean_closure_set(v___f_3517_, 7, v_a_3491_);
v___x_3518_ = 0;
v___x_3519_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3510_, v_binderInfo_3513_, v_a_3515_, v___f_3517_, v___x_3518_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec_ref(v_a_3474_);
return v___x_3519_;
}
else
{
lean_dec_ref(v_body_3512_);
lean_dec(v_binderName_3510_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
return v___x_3514_;
}
}
case 8:
{
lean_object* v_declName_3520_; lean_object* v_type_3521_; lean_object* v_value_3522_; lean_object* v_body_3523_; uint8_t v_nondep_3524_; lean_object* v___x_3525_; 
lean_dec(v_a_3491_);
v_declName_3520_ = lean_ctor_get(v_e_3470_, 0);
lean_inc(v_declName_3520_);
v_type_3521_ = lean_ctor_get(v_e_3470_, 1);
lean_inc_ref(v_type_3521_);
v_value_3522_ = lean_ctor_get(v_e_3470_, 2);
lean_inc_ref(v_value_3522_);
v_body_3523_ = lean_ctor_get(v_e_3470_, 3);
lean_inc_ref(v_body_3523_);
v_nondep_3524_ = lean_ctor_get_uint8(v_e_3470_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3470_);
lean_inc_ref(v_a_3474_);
lean_inc_ref(v_below_3469_);
lean_inc_ref(v_containsRecFn_3468_);
lean_inc_ref(v_recFnNames_3467_);
lean_inc_ref(v_positions_3466_);
lean_inc_ref(v_recArgInfos_3465_);
v___x_3525_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3465_, v_positions_3466_, v_recFnNames_3467_, v_containsRecFn_3468_, v_below_3469_, v_type_3521_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3527_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v___x_3525_);
lean_inc_ref(v_a_3474_);
lean_inc_ref(v_below_3469_);
lean_inc_ref(v_containsRecFn_3468_);
lean_inc_ref(v_recFnNames_3467_);
lean_inc_ref(v_positions_3466_);
lean_inc_ref(v_recArgInfos_3465_);
v___x_3527_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3465_, v_positions_3466_, v_recFnNames_3467_, v_containsRecFn_3468_, v_below_3469_, v_value_3522_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___f_3529_; uint8_t v___x_3530_; lean_object* v___x_3531_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref(v___x_3527_);
v___f_3529_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3529_, 0, v_body_3523_);
lean_closure_set(v___f_3529_, 1, v_recArgInfos_3465_);
lean_closure_set(v___f_3529_, 2, v_positions_3466_);
lean_closure_set(v___f_3529_, 3, v_recFnNames_3467_);
lean_closure_set(v___f_3529_, 4, v_containsRecFn_3468_);
lean_closure_set(v___f_3529_, 5, v_below_3469_);
v___x_3530_ = 0;
v___x_3531_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3520_, v_a_3526_, v_a_3528_, v___f_3529_, v_nondep_3524_, v___x_3530_, v___x_3499_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec_ref(v_a_3474_);
return v___x_3531_;
}
else
{
lean_dec(v_a_3526_);
lean_dec_ref(v_body_3523_);
lean_dec(v_declName_3520_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
return v___x_3527_;
}
}
else
{
lean_dec_ref(v_body_3523_);
lean_dec_ref(v_value_3522_);
lean_dec(v_declName_3520_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
return v___x_3525_;
}
}
case 10:
{
lean_object* v_data_3532_; lean_object* v_expr_3533_; lean_object* v___x_3534_; 
lean_dec(v_a_3491_);
v_data_3532_ = lean_ctor_get(v_e_3470_, 0);
lean_inc(v_data_3532_);
v_expr_3533_ = lean_ctor_get(v_e_3470_, 1);
lean_inc_ref(v_expr_3533_);
v___x_3534_ = l_Lean_getRecAppSyntax_x3f(v_e_3470_);
lean_dec_ref(v_e_3470_);
if (lean_obj_tag(v___x_3534_) == 1)
{
lean_object* v_val_3535_; lean_object* v_fileName_3536_; lean_object* v_fileMap_3537_; lean_object* v_options_3538_; lean_object* v_currRecDepth_3539_; lean_object* v_maxRecDepth_3540_; lean_object* v_ref_3541_; lean_object* v_currNamespace_3542_; lean_object* v_openDecls_3543_; lean_object* v_initHeartbeats_3544_; lean_object* v_maxHeartbeats_3545_; lean_object* v_quotContext_3546_; lean_object* v_currMacroScope_3547_; uint8_t v_diag_3548_; lean_object* v_cancelTk_x3f_3549_; uint8_t v_suppressElabErrors_3550_; lean_object* v_inheritedTraceOptions_3551_; lean_object* v_ref_3552_; lean_object* v___x_3553_; 
lean_dec(v_data_3532_);
v_val_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_val_3535_);
lean_dec_ref(v___x_3534_);
v_fileName_3536_ = lean_ctor_get(v_a_3474_, 0);
lean_inc_ref(v_fileName_3536_);
v_fileMap_3537_ = lean_ctor_get(v_a_3474_, 1);
lean_inc_ref(v_fileMap_3537_);
v_options_3538_ = lean_ctor_get(v_a_3474_, 2);
lean_inc_ref(v_options_3538_);
v_currRecDepth_3539_ = lean_ctor_get(v_a_3474_, 3);
lean_inc(v_currRecDepth_3539_);
v_maxRecDepth_3540_ = lean_ctor_get(v_a_3474_, 4);
lean_inc(v_maxRecDepth_3540_);
v_ref_3541_ = lean_ctor_get(v_a_3474_, 5);
lean_inc(v_ref_3541_);
v_currNamespace_3542_ = lean_ctor_get(v_a_3474_, 6);
lean_inc(v_currNamespace_3542_);
v_openDecls_3543_ = lean_ctor_get(v_a_3474_, 7);
lean_inc(v_openDecls_3543_);
v_initHeartbeats_3544_ = lean_ctor_get(v_a_3474_, 8);
lean_inc(v_initHeartbeats_3544_);
v_maxHeartbeats_3545_ = lean_ctor_get(v_a_3474_, 9);
lean_inc(v_maxHeartbeats_3545_);
v_quotContext_3546_ = lean_ctor_get(v_a_3474_, 10);
lean_inc(v_quotContext_3546_);
v_currMacroScope_3547_ = lean_ctor_get(v_a_3474_, 11);
lean_inc(v_currMacroScope_3547_);
v_diag_3548_ = lean_ctor_get_uint8(v_a_3474_, sizeof(void*)*14);
v_cancelTk_x3f_3549_ = lean_ctor_get(v_a_3474_, 12);
lean_inc(v_cancelTk_x3f_3549_);
v_suppressElabErrors_3550_ = lean_ctor_get_uint8(v_a_3474_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3551_ = lean_ctor_get(v_a_3474_, 13);
lean_inc_ref(v_inheritedTraceOptions_3551_);
lean_dec_ref(v_a_3474_);
v_ref_3552_ = l_Lean_replaceRef(v_val_3535_, v_ref_3541_);
lean_dec(v_ref_3541_);
lean_dec(v_val_3535_);
v___x_3553_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3553_, 0, v_fileName_3536_);
lean_ctor_set(v___x_3553_, 1, v_fileMap_3537_);
lean_ctor_set(v___x_3553_, 2, v_options_3538_);
lean_ctor_set(v___x_3553_, 3, v_currRecDepth_3539_);
lean_ctor_set(v___x_3553_, 4, v_maxRecDepth_3540_);
lean_ctor_set(v___x_3553_, 5, v_ref_3552_);
lean_ctor_set(v___x_3553_, 6, v_currNamespace_3542_);
lean_ctor_set(v___x_3553_, 7, v_openDecls_3543_);
lean_ctor_set(v___x_3553_, 8, v_initHeartbeats_3544_);
lean_ctor_set(v___x_3553_, 9, v_maxHeartbeats_3545_);
lean_ctor_set(v___x_3553_, 10, v_quotContext_3546_);
lean_ctor_set(v___x_3553_, 11, v_currMacroScope_3547_);
lean_ctor_set(v___x_3553_, 12, v_cancelTk_x3f_3549_);
lean_ctor_set(v___x_3553_, 13, v_inheritedTraceOptions_3551_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*14, v_diag_3548_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*14 + 1, v_suppressElabErrors_3550_);
v_e_3470_ = v_expr_3533_;
v_a_3474_ = v___x_3553_;
goto _start;
}
else
{
lean_object* v___x_3555_; 
lean_dec(v___x_3534_);
v___x_3555_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3465_, v_positions_3466_, v_recFnNames_3467_, v_containsRecFn_3468_, v_below_3469_, v_expr_3533_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3564_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3564_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3564_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; lean_object* v___x_3562_; 
v___x_3560_ = l_Lean_mkMData(v_data_3532_, v_a_3556_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3560_);
v___x_3562_ = v___x_3558_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
else
{
lean_dec(v_data_3532_);
return v___x_3555_;
}
}
}
case 11:
{
lean_object* v_typeName_3565_; lean_object* v_idx_3566_; lean_object* v_struct_3567_; lean_object* v___x_3568_; 
lean_dec(v_a_3491_);
v_typeName_3565_ = lean_ctor_get(v_e_3470_, 0);
lean_inc(v_typeName_3565_);
v_idx_3566_ = lean_ctor_get(v_e_3470_, 1);
lean_inc(v_idx_3566_);
v_struct_3567_ = lean_ctor_get(v_e_3470_, 2);
lean_inc_ref(v_struct_3567_);
lean_dec_ref(v_e_3470_);
v___x_3568_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3465_, v_positions_3466_, v_recFnNames_3467_, v_containsRecFn_3468_, v_below_3469_, v_struct_3567_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3577_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3577_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3577_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3573_ = l_Lean_mkProj(v_typeName_3565_, v_idx_3566_, v_a_3569_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 0, v___x_3573_);
v___x_3575_ = v___x_3571_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
else
{
lean_dec(v_idx_3566_);
lean_dec(v_typeName_3565_);
return v___x_3568_;
}
}
case 5:
{
uint8_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_unbox(v_a_3491_);
lean_inc_ref(v_e_3470_);
v___x_3579_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3470_, v___x_3578_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref(v___x_3579_);
if (lean_obj_tag(v_a_3580_) == 0)
{
lean_dec(v_a_3491_);
v_e_3478_ = v_e_3470_;
v___y_3479_ = v_a_3471_;
v___y_3480_ = v_a_3472_;
v___y_3481_ = v_a_3473_;
v___y_3482_ = v_a_3474_;
v___y_3483_ = v_a_3475_;
goto v___jp_3477_;
}
else
{
lean_object* v_val_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; 
v_val_3581_ = lean_ctor_get(v_a_3580_, 0);
lean_inc(v_val_3581_);
lean_dec_ref(v_a_3580_);
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = lean_array_get_size(v_recArgInfos_3465_);
v___x_3584_ = lean_nat_dec_lt(v___x_3582_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_dec(v_val_3581_);
lean_dec(v_a_3491_);
v_e_3478_ = v_e_3470_;
v___y_3479_ = v_a_3471_;
v___y_3480_ = v_a_3472_;
v___y_3481_ = v_a_3473_;
v___y_3482_ = v_a_3474_;
v___y_3483_ = v_a_3475_;
goto v___jp_3477_;
}
else
{
if (v___x_3584_ == 0)
{
lean_dec(v_val_3581_);
lean_dec(v_a_3491_);
v_e_3478_ = v_e_3470_;
v___y_3479_ = v_a_3471_;
v___y_3480_ = v_a_3472_;
v___y_3481_ = v_a_3473_;
v___y_3482_ = v_a_3474_;
v___y_3483_ = v_a_3475_;
goto v___jp_3477_;
}
else
{
size_t v___x_3585_; size_t v___x_3586_; uint8_t v___x_3587_; 
v___x_3585_ = ((size_t)0ULL);
v___x_3586_ = lean_usize_of_nat(v___x_3583_);
v___x_3587_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3470_, v_recArgInfos_3465_, v___x_3585_, v___x_3586_);
if (v___x_3587_ == 0)
{
lean_dec(v_val_3581_);
lean_dec(v_a_3491_);
v_e_3478_ = v_e_3470_;
v___y_3479_ = v_a_3471_;
v___y_3480_ = v_a_3472_;
v___y_3481_ = v_a_3473_;
v___y_3482_ = v_a_3474_;
v___y_3483_ = v_a_3475_;
goto v___jp_3477_;
}
else
{
lean_object* v___x_3588_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___x_3657_; 
v___x_3588_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3657_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v___x_3588_, v_a_3474_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; uint8_t v___x_3659_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref(v___x_3657_);
v___x_3659_ = lean_unbox(v_a_3658_);
lean_dec(v_a_3658_);
if (v___x_3659_ == 0)
{
v___y_3590_ = v_a_3471_;
v___y_3591_ = v_a_3472_;
v___y_3592_ = v_a_3473_;
v___y_3593_ = v_a_3474_;
v___y_3594_ = v_a_3475_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3660_; 
lean_inc(v_a_3475_);
lean_inc_ref(v_a_3474_);
lean_inc(v_a_3473_);
lean_inc_ref(v_a_3472_);
lean_inc_ref(v_below_3469_);
v___x_3660_ = lean_infer_type(v_below_3469_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3660_);
v___x_3662_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3469_);
v___x_3663_ = l_Lean_MessageData_ofExpr(v_below_3469_);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = l_Lean_MessageData_ofExpr(v_a_3661_);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v___x_3588_, v___x_3668_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_dec_ref(v___x_3669_);
v___y_3590_ = v_a_3471_;
v___y_3591_ = v_a_3472_;
v___y_3592_ = v_a_3473_;
v___y_3593_ = v_a_3474_;
v___y_3594_ = v_a_3475_;
goto v___jp_3589_;
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v_val_3581_);
lean_dec_ref(v_e_3470_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
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
}
else
{
lean_dec(v_val_3581_);
lean_dec_ref(v_e_3470_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
return v___x_3660_;
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v_val_3581_);
lean_dec_ref(v_e_3470_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
v_a_3678_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3657_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3657_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
v___jp_3589_:
{
lean_object* v___x_3595_; 
lean_inc_ref(v_below_3469_);
v___x_3595_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3581_, v_below_3469_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3595_);
if (lean_obj_tag(v_a_3596_) == 1)
{
lean_object* v_val_3597_; lean_object* v_toMatcherInfo_3598_; lean_object* v_matcherName_3599_; lean_object* v_matcherLevels_3600_; lean_object* v_params_3601_; lean_object* v_motive_3602_; lean_object* v_discrs_3603_; lean_object* v_alts_3604_; lean_object* v_remaining_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; lean_object* v___x_3609_; 
lean_dec_ref(v_below_3469_);
v_val_3597_ = lean_ctor_get(v_a_3596_, 0);
lean_inc(v_val_3597_);
lean_dec_ref(v_a_3596_);
v_toMatcherInfo_3598_ = lean_ctor_get(v_val_3597_, 0);
lean_inc_ref(v_toMatcherInfo_3598_);
v_matcherName_3599_ = lean_ctor_get(v_val_3597_, 1);
lean_inc(v_matcherName_3599_);
v_matcherLevels_3600_ = lean_ctor_get(v_val_3597_, 2);
lean_inc_ref(v_matcherLevels_3600_);
v_params_3601_ = lean_ctor_get(v_val_3597_, 3);
lean_inc_ref(v_params_3601_);
v_motive_3602_ = lean_ctor_get(v_val_3597_, 4);
lean_inc_ref(v_motive_3602_);
v_discrs_3603_ = lean_ctor_get(v_val_3597_, 5);
lean_inc_ref(v_discrs_3603_);
v_alts_3604_ = lean_ctor_get(v_val_3597_, 6);
lean_inc_ref(v_alts_3604_);
v_remaining_3605_ = lean_ctor_get(v_val_3597_, 7);
lean_inc_ref(v_remaining_3605_);
v___x_3606_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3597_);
v___x_3607_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3608_ = lean_unbox(v_a_3491_);
lean_dec(v_a_3491_);
v___x_3609_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11(v_recArgInfos_3465_, v_positions_3466_, v_recFnNames_3467_, v_containsRecFn_3468_, v___x_3608_, v_e_3470_, v_alts_3604_, v___x_3606_, v___x_3582_, v___x_3607_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec_ref(v___x_3606_);
lean_dec_ref(v_alts_3604_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3619_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3619_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3619_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3614_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3614_, 0, v_toMatcherInfo_3598_);
lean_ctor_set(v___x_3614_, 1, v_matcherName_3599_);
lean_ctor_set(v___x_3614_, 2, v_matcherLevels_3600_);
lean_ctor_set(v___x_3614_, 3, v_params_3601_);
lean_ctor_set(v___x_3614_, 4, v_motive_3602_);
lean_ctor_set(v___x_3614_, 5, v_discrs_3603_);
lean_ctor_set(v___x_3614_, 6, v_a_3610_);
lean_ctor_set(v___x_3614_, 7, v_remaining_3605_);
v___x_3615_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3614_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v___x_3615_);
v___x_3617_ = v___x_3612_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec_ref(v_remaining_3605_);
lean_dec_ref(v_discrs_3603_);
lean_dec_ref(v_motive_3602_);
lean_dec_ref(v_params_3601_);
lean_dec_ref(v_matcherLevels_3600_);
lean_dec(v_matcherName_3599_);
lean_dec_ref(v_toMatcherInfo_3598_);
v_a_3620_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3609_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3609_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_object* v___x_3628_; 
lean_dec(v_a_3596_);
lean_dec(v_a_3491_);
v___x_3628_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7___redArg(v___x_3588_, v___y_3593_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; uint8_t v___x_3630_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref(v___x_3628_);
v___x_3630_ = lean_unbox(v_a_3629_);
lean_dec(v_a_3629_);
if (v___x_3630_ == 0)
{
v_e_3478_ = v_e_3470_;
v___y_3479_ = v___y_3590_;
v___y_3480_ = v___y_3591_;
v___y_3481_ = v___y_3592_;
v___y_3482_ = v___y_3593_;
v___y_3483_ = v___y_3594_;
goto v___jp_3477_;
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3632_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v___x_3588_, v___x_3631_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_dec_ref(v___x_3632_);
v_e_3478_ = v_e_3470_;
v___y_3479_ = v___y_3590_;
v___y_3480_ = v___y_3591_;
v___y_3481_ = v___y_3592_;
v___y_3482_ = v___y_3593_;
v___y_3483_ = v___y_3594_;
goto v___jp_3477_;
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec_ref(v___y_3593_);
lean_dec_ref(v_e_3470_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec_ref(v___y_3593_);
lean_dec_ref(v_e_3470_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
v_a_3641_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3628_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3628_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
else
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_dec_ref(v___y_3593_);
lean_dec_ref(v_e_3470_);
lean_dec(v_a_3491_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
v_a_3649_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3595_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3595_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
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
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec_ref(v_e_3470_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
v_a_3686_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3579_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3579_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
default: 
{
lean_object* v___x_3694_; 
lean_dec(v_a_3491_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
lean_inc_ref(v_e_3470_);
v___x_3694_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3467_, v_e_3470_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec_ref(v_a_3474_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v___x_3694_, 0);
lean_dec(v_unused_3702_);
v___x_3696_ = v___x_3694_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_dec(v___x_3694_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v_e_3470_);
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_e_3470_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v_e_3470_);
v_a_3703_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3694_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3694_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
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
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec_ref(v_a_3474_);
lean_dec_ref(v_e_3470_);
lean_dec_ref(v_below_3469_);
lean_dec_ref(v_containsRecFn_3468_);
lean_dec_ref(v_recFnNames_3467_);
lean_dec_ref(v_positions_3466_);
lean_dec_ref(v_recArgInfos_3465_);
v_a_3712_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3490_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3490_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
v___jp_3477_:
{
lean_object* v_dummy_3484_; lean_object* v_nargs_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_dummy_3484_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0);
v_nargs_3485_ = l_Lean_Expr_getAppNumArgs(v_e_3478_);
lean_inc(v_nargs_3485_);
v___x_3486_ = lean_mk_array(v_nargs_3485_, v_dummy_3484_);
v___x_3487_ = lean_unsigned_to_nat(1u);
v___x_3488_ = lean_nat_sub(v_nargs_3485_, v___x_3487_);
lean_dec(v_nargs_3485_);
lean_inc_ref(v_e_3478_);
v___x_3489_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3465_, v_positions_3466_, v_recFnNames_3467_, v_containsRecFn_3468_, v_below_3469_, v_e_3478_, v_e_3478_, v___x_3486_, v___x_3488_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec_ref(v___y_3482_);
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3720_, lean_object* v_recArgInfos_3721_, lean_object* v_positions_3722_, lean_object* v_recFnNames_3723_, lean_object* v_containsRecFn_3724_, lean_object* v_below_3725_, lean_object* v_x_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = lean_expr_instantiate1(v_body_3720_, v_x_3726_);
lean_inc_ref(v___y_3730_);
v___x_3734_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3721_, v_positions_3722_, v_recFnNames_3723_, v_containsRecFn_3724_, v_below_3725_, v___x_3733_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3735_, lean_object* v_positions_3736_, lean_object* v_recFnNames_3737_, lean_object* v_containsRecFn_3738_, lean_object* v_below_3739_, lean_object* v_sz_3740_, lean_object* v_i_3741_, lean_object* v_bs_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
size_t v_sz_boxed_3749_; size_t v_i_boxed_3750_; lean_object* v_res_3751_; 
v_sz_boxed_3749_ = lean_unbox_usize(v_sz_3740_);
lean_dec(v_sz_3740_);
v_i_boxed_3750_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3735_, v_positions_3736_, v_recFnNames_3737_, v_containsRecFn_3738_, v_below_3739_, v_sz_boxed_3749_, v_i_boxed_3750_, v_bs_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11___boxed(lean_object* v_recArgInfos_3752_, lean_object* v_positions_3753_, lean_object* v_recFnNames_3754_, lean_object* v_containsRecFn_3755_, lean_object* v_a_3756_, lean_object* v_e_3757_, lean_object* v_as_3758_, lean_object* v_bs_3759_, lean_object* v_i_3760_, lean_object* v_cs_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
uint8_t v_a_31309__boxed_3768_; lean_object* v_res_3769_; 
v_a_31309__boxed_3768_ = lean_unbox(v_a_3756_);
v_res_3769_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__11(v_recArgInfos_3752_, v_positions_3753_, v_recFnNames_3754_, v_containsRecFn_3755_, v_a_31309__boxed_3768_, v_e_3757_, v_as_3758_, v_bs_3759_, v_i_3760_, v_cs_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v_bs_3759_);
lean_dec_ref(v_as_3758_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3770_, lean_object* v_positions_3771_, lean_object* v_recFnNames_3772_, lean_object* v_containsRecFn_3773_, lean_object* v_below_3774_, lean_object* v_e_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3770_, v_positions_3771_, v_recFnNames_3772_, v_containsRecFn_3773_, v_below_3774_, v_e_3775_, v_x_3776_, v_x_3777_, v_x_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3786_, lean_object* v_positions_3787_, lean_object* v_recFnNames_3788_, lean_object* v_containsRecFn_3789_, lean_object* v_below_3790_, lean_object* v_e_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3786_, v_positions_3787_, v_recFnNames_3788_, v_containsRecFn_3789_, v_below_3790_, v_e_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec(v_a_3796_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3799_, lean_object* v_msg_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3800_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3808_, lean_object* v_msg_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3808_, v_msg_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3817_, lean_object* v_name_3818_, lean_object* v_type_3819_, lean_object* v_val_3820_, lean_object* v_k_3821_, uint8_t v_nondep_3822_, uint8_t v_kind_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3818_, v_type_3819_, v_val_3820_, v_k_3821_, v_nondep_3822_, v_kind_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_name_3832_, lean_object* v_type_3833_, lean_object* v_val_3834_, lean_object* v_k_3835_, lean_object* v_nondep_3836_, lean_object* v_kind_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
uint8_t v_nondep_boxed_3844_; uint8_t v_kind_boxed_3845_; lean_object* v_res_3846_; 
v_nondep_boxed_3844_ = lean_unbox(v_nondep_3836_);
v_kind_boxed_3845_ = lean_unbox(v_kind_3837_);
v_res_3846_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3831_, v_name_3832_, v_type_3833_, v_val_3834_, v_k_3835_, v_nondep_boxed_3844_, v_kind_boxed_3845_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3847_, v___y_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_cls_3863_, lean_object* v_msg_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_cls_3863_, v_msg_3864_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_cls_3872_, lean_object* v_msg_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_cls_3872_, v_msg_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9(lean_object* v_00_u03b1_3881_, lean_object* v_constName_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___redArg(v_constName_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_constName_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9(v_00_u03b1_3890_, v_constName_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16(lean_object* v_00_u03b1_3899_, lean_object* v_ref_3900_, lean_object* v_constName_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___redArg(v_ref_3900_, v_constName_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3909_, lean_object* v_ref_3910_, lean_object* v_constName_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16(v_00_u03b1_3909_, v_ref_3910_, v_constName_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec(v_ref_3910_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18(lean_object* v_00_u03b1_3919_, lean_object* v_ref_3920_, lean_object* v_msg_3921_, lean_object* v_declHint_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___redArg(v_ref_3920_, v_msg_3921_, v_declHint_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18___boxed(lean_object* v_00_u03b1_3930_, lean_object* v_ref_3931_, lean_object* v_msg_3932_, lean_object* v_declHint_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18(v_00_u03b1_3930_, v_ref_3931_, v_msg_3932_, v_declHint_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec(v_ref_3931_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_3941_, lean_object* v_declHint_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_3941_, v_declHint_3942_, v___y_3947_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_3950_, lean_object* v_declHint_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__19_spec__20(v_msg_3950_, v_declHint_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_3959_, lean_object* v_ref_3960_, lean_object* v_msg_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___redArg(v_ref_3960_, v_msg_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_3969_, lean_object* v_ref_3970_, lean_object* v_msg_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__9_spec__16_spec__18_spec__20(v_00_u03b1_3969_, v_ref_3970_, v_msg_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec(v_ref_3970_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3979_, lean_object* v_e_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v_fst_3989_; lean_object* v_snd_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3987_ = lean_st_ref_take(v___y_3981_);
v___x_3988_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3979_, v_e_3980_, v___x_3987_);
v_fst_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_fst_3989_);
v_snd_3990_ = lean_ctor_get(v___x_3988_, 1);
lean_inc(v_snd_3990_);
lean_dec_ref(v___x_3988_);
v___x_3991_ = lean_st_ref_set(v___y_3981_, v_snd_3990_);
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v_fst_3989_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3993_, lean_object* v_e_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3993_, v_e_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v_recFnNames_3993_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_4002_, size_t v_i_4003_, lean_object* v_bs_4004_){
_start:
{
uint8_t v___x_4005_; 
v___x_4005_ = lean_usize_dec_lt(v_i_4003_, v_sz_4002_);
if (v___x_4005_ == 0)
{
return v_bs_4004_;
}
else
{
lean_object* v_v_4006_; lean_object* v_fnName_4007_; lean_object* v___x_4008_; lean_object* v_bs_x27_4009_; size_t v___x_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
v_v_4006_ = lean_array_uget_borrowed(v_bs_4004_, v_i_4003_);
v_fnName_4007_ = lean_ctor_get(v_v_4006_, 0);
lean_inc(v_fnName_4007_);
v___x_4008_ = lean_unsigned_to_nat(0u);
v_bs_x27_4009_ = lean_array_uset(v_bs_4004_, v_i_4003_, v___x_4008_);
v___x_4010_ = ((size_t)1ULL);
v___x_4011_ = lean_usize_add(v_i_4003_, v___x_4010_);
v___x_4012_ = lean_array_uset(v_bs_x27_4009_, v_i_4003_, v_fnName_4007_);
v_i_4003_ = v___x_4011_;
v_bs_4004_ = v___x_4012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_4014_, lean_object* v_i_4015_, lean_object* v_bs_4016_){
_start:
{
size_t v_sz_boxed_4017_; size_t v_i_boxed_4018_; lean_object* v_res_4019_; 
v_sz_boxed_4017_ = lean_unbox_usize(v_sz_4014_);
lean_dec(v_sz_4014_);
v_i_boxed_4018_ = lean_unbox_usize(v_i_4015_);
lean_dec(v_i_4015_);
v_res_4019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_4017_, v_i_boxed_4018_, v_bs_4016_);
return v_res_4019_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4020_ = lean_box(0);
v___x_4021_ = lean_unsigned_to_nat(16u);
v___x_4022_ = lean_mk_array(v___x_4021_, v___x_4020_);
return v___x_4022_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4023_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_4024_ = lean_unsigned_to_nat(0u);
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
lean_ctor_set(v___x_4025_, 1, v___x_4023_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_4026_, lean_object* v_positions_4027_, lean_object* v_below_4028_, lean_object* v_e_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; size_t v_sz_4037_; size_t v___x_4038_; lean_object* v_recFnNames_4039_; lean_object* v_containsRecFn_4040_; lean_object* v___x_4041_; 
v___x_4035_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_4036_ = lean_st_mk_ref(v___x_4035_);
v_sz_4037_ = lean_array_size(v_recArgInfos_4026_);
v___x_4038_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_4026_);
v_recFnNames_4039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_4037_, v___x_4038_, v_recArgInfos_4026_);
lean_inc_ref(v_recFnNames_4039_);
v_containsRecFn_4040_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_4040_, 0, v_recFnNames_4039_);
lean_inc_ref(v_a_4032_);
v___x_4041_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_4026_, v_positions_4027_, v_recFnNames_4039_, v_containsRecFn_4040_, v_below_4028_, v_e_4029_, v___x_4036_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4050_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4050_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4050_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4046_ = lean_st_ref_get(v___x_4036_);
lean_dec(v___x_4036_);
lean_dec(v___x_4046_);
if (v_isShared_4045_ == 0)
{
v___x_4048_ = v___x_4044_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4042_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
else
{
lean_dec(v___x_4036_);
return v___x_4041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_4051_, lean_object* v_positions_4052_, lean_object* v_below_4053_, lean_object* v_e_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4051_, v_positions_4052_, v_below_4053_, v_e_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_4061_, lean_object* v_k_4062_, uint8_t v_cleanupAnnotations_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___f_4069_; uint8_t v___x_4070_; uint8_t v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___f_4069_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4069_, 0, v_k_4062_);
v___x_4070_ = 1;
v___x_4071_ = 0;
v___x_4072_ = lean_box(0);
v___x_4073_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4061_, v___x_4070_, v___x_4071_, v___x_4070_, v___x_4071_, v___x_4072_, v___f_4069_, v_cleanupAnnotations_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
v_a_4082_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4073_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4073_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4090_, lean_object* v_k_4091_, lean_object* v_cleanupAnnotations_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4098_; lean_object* v_res_4099_; 
v_cleanupAnnotations_boxed_4098_ = lean_unbox(v_cleanupAnnotations_4092_);
v_res_4099_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4090_, v_k_4091_, v_cleanupAnnotations_boxed_4098_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4100_, lean_object* v_e_4101_, lean_object* v_k_4102_, uint8_t v_cleanupAnnotations_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4101_, v_k_4102_, v_cleanupAnnotations_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4110_, lean_object* v_e_4111_, lean_object* v_k_4112_, lean_object* v_cleanupAnnotations_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4119_; lean_object* v_res_4120_; 
v_cleanupAnnotations_boxed_4119_ = lean_unbox(v_cleanupAnnotations_4113_);
v_res_4120_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4110_, v_e_4111_, v_k_4112_, v_cleanupAnnotations_boxed_4119_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4121_, lean_object* v_recArgInfo_4122_, lean_object* v_xs_4123_, lean_object* v___value_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v___x_4130_; 
v___x_4130_ = l_Lean_Meta_instantiateForall(v_type_4121_, v_xs_4123_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4132_; lean_object* v_fst_4133_; lean_object* v_snd_4134_; uint8_t v___x_4135_; uint8_t v___x_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref(v___x_4130_);
v___x_4132_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4122_, v_xs_4123_);
v_fst_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_fst_4133_);
v_snd_4134_ = lean_ctor_get(v___x_4132_, 1);
lean_inc(v_snd_4134_);
lean_dec_ref(v___x_4132_);
v___x_4135_ = 0;
v___x_4136_ = 1;
v___x_4137_ = 1;
v___x_4138_ = l_Lean_Meta_mkForallFVars(v_snd_4134_, v_a_4131_, v___x_4135_, v___x_4136_, v___x_4136_, v___x_4137_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v_snd_4134_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref(v___x_4138_);
v___x_4140_ = l_Lean_Meta_mkLambdaFVars(v_fst_4133_, v_a_4139_, v___x_4135_, v___x_4136_, v___x_4135_, v___x_4136_, v___x_4137_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v_fst_4133_);
return v___x_4140_;
}
else
{
lean_dec(v_fst_4133_);
return v___x_4138_;
}
}
else
{
lean_dec_ref(v_xs_4123_);
lean_dec_ref(v_recArgInfo_4122_);
return v___x_4130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4141_, lean_object* v_recArgInfo_4142_, lean_object* v_xs_4143_, lean_object* v___value_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4141_, v_recArgInfo_4142_, v_xs_4143_, v___value_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec_ref(v___value_4144_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4151_, lean_object* v_value_4152_, lean_object* v_type_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v___f_4159_; uint8_t v___x_4160_; lean_object* v___x_4161_; 
v___f_4159_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4159_, 0, v_type_4153_);
lean_closure_set(v___f_4159_, 1, v_recArgInfo_4151_);
v___x_4160_ = 0;
v___x_4161_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4152_, v___f_4159_, v___x_4160_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4162_, lean_object* v_value_4163_, lean_object* v_type_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4162_, v_value_4163_, v_type_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4171_, lean_object* v_maxFVars_x3f_4172_, lean_object* v_k_4173_, uint8_t v_cleanupAnnotations_4174_, uint8_t v_whnfType_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___f_4181_; lean_object* v___x_4182_; 
v___f_4181_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4181_, 0, v_k_4173_);
v___x_4182_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4171_, v_maxFVars_x3f_4172_, v___f_4181_, v_cleanupAnnotations_4174_, v_whnfType_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4182_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
v_a_4191_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4182_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4182_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4199_, lean_object* v_maxFVars_x3f_4200_, lean_object* v_k_4201_, lean_object* v_cleanupAnnotations_4202_, lean_object* v_whnfType_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4209_; uint8_t v_whnfType_boxed_4210_; lean_object* v_res_4211_; 
v_cleanupAnnotations_boxed_4209_ = lean_unbox(v_cleanupAnnotations_4202_);
v_whnfType_boxed_4210_ = lean_unbox(v_whnfType_4203_);
v_res_4211_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4199_, v_maxFVars_x3f_4200_, v_k_4201_, v_cleanupAnnotations_boxed_4209_, v_whnfType_boxed_4210_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4212_, lean_object* v_type_4213_, lean_object* v_maxFVars_x3f_4214_, lean_object* v_k_4215_, uint8_t v_cleanupAnnotations_4216_, uint8_t v_whnfType_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4213_, v_maxFVars_x3f_4214_, v_k_4215_, v_cleanupAnnotations_4216_, v_whnfType_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4224_, lean_object* v_type_4225_, lean_object* v_maxFVars_x3f_4226_, lean_object* v_k_4227_, lean_object* v_cleanupAnnotations_4228_, lean_object* v_whnfType_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4235_; uint8_t v_whnfType_boxed_4236_; lean_object* v_res_4237_; 
v_cleanupAnnotations_boxed_4235_ = lean_unbox(v_cleanupAnnotations_4228_);
v_whnfType_boxed_4236_ = lean_unbox(v_whnfType_4229_);
v_res_4237_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4224_, v_type_4225_, v_maxFVars_x3f_4226_, v_k_4227_, v_cleanupAnnotations_boxed_4235_, v_whnfType_boxed_4236_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4238_, lean_object* v_recArgInfos_4239_, lean_object* v_positions_4240_, lean_object* v_value_4241_, lean_object* v_fst_4242_, lean_object* v_snd_4243_, lean_object* v_below_4244_, lean_object* v_x_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = lean_unsigned_to_nat(0u);
v___x_4252_ = lean_array_get_borrowed(v___x_4238_, v_below_4244_, v___x_4251_);
lean_inc(v___x_4252_);
v___x_4253_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4239_, v_positions_4240_, v___x_4252_, v_value_4241_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; uint8_t v___x_4260_; uint8_t v___x_4261_; uint8_t v___x_4262_; lean_object* v___x_4263_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref(v___x_4253_);
v___x_4255_ = lean_unsigned_to_nat(1u);
v___x_4256_ = lean_mk_empty_array_with_capacity(v___x_4255_);
lean_inc(v___x_4252_);
v___x_4257_ = lean_array_push(v___x_4256_, v___x_4252_);
v___x_4258_ = l_Array_append___redArg(v_fst_4242_, v___x_4257_);
lean_dec_ref(v___x_4257_);
v___x_4259_ = l_Array_append___redArg(v___x_4258_, v_snd_4243_);
v___x_4260_ = 0;
v___x_4261_ = 1;
v___x_4262_ = 1;
v___x_4263_ = l_Lean_Meta_mkLambdaFVars(v___x_4259_, v_a_4254_, v___x_4260_, v___x_4261_, v___x_4260_, v___x_4261_, v___x_4262_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
lean_dec_ref(v___x_4259_);
return v___x_4263_;
}
else
{
lean_dec_ref(v_fst_4242_);
return v___x_4253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4264_, lean_object* v_recArgInfos_4265_, lean_object* v_positions_4266_, lean_object* v_value_4267_, lean_object* v_fst_4268_, lean_object* v_snd_4269_, lean_object* v_below_4270_, lean_object* v_x_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4264_, v_recArgInfos_4265_, v_positions_4266_, v_value_4267_, v_fst_4268_, v_snd_4269_, v_below_4270_, v_x_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec_ref(v_x_4271_);
lean_dec_ref(v_below_4270_);
lean_dec_ref(v_snd_4269_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4280_, lean_object* v_FType_4281_, lean_object* v___x_4282_, lean_object* v_recArgInfos_4283_, lean_object* v_positions_4284_, lean_object* v_xs_4285_, lean_object* v_value_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v___x_4292_; lean_object* v_fst_4293_; lean_object* v_snd_4294_; lean_object* v___x_4295_; 
v___x_4292_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4280_, v_xs_4285_);
v_fst_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_fst_4293_);
v_snd_4294_ = lean_ctor_get(v___x_4292_, 1);
lean_inc(v_snd_4294_);
lean_dec_ref(v___x_4292_);
v___x_4295_ = l_Lean_Meta_instantiateForall(v_FType_4281_, v_fst_4293_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___f_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; lean_object* v___x_4300_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref(v___x_4295_);
v___f_4297_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4297_, 0, v___x_4282_);
lean_closure_set(v___f_4297_, 1, v_recArgInfos_4283_);
lean_closure_set(v___f_4297_, 2, v_positions_4284_);
lean_closure_set(v___f_4297_, 3, v_value_4286_);
lean_closure_set(v___f_4297_, 4, v_fst_4293_);
lean_closure_set(v___f_4297_, 5, v_snd_4294_);
v___x_4298_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4299_ = 0;
v___x_4300_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4296_, v___x_4298_, v___f_4297_, v___x_4299_, v___x_4299_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
return v___x_4300_;
}
else
{
lean_dec(v_snd_4294_);
lean_dec(v_fst_4293_);
lean_dec_ref(v_value_4286_);
lean_dec_ref(v_positions_4284_);
lean_dec_ref(v_recArgInfos_4283_);
lean_dec_ref(v___x_4282_);
return v___x_4295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4301_, lean_object* v_FType_4302_, lean_object* v___x_4303_, lean_object* v_recArgInfos_4304_, lean_object* v_positions_4305_, lean_object* v_xs_4306_, lean_object* v_value_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4301_, v_FType_4302_, v___x_4303_, v_recArgInfos_4304_, v_positions_4305_, v_xs_4306_, v_value_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4314_, lean_object* v_positions_4315_, lean_object* v_recArgInfo_4316_, lean_object* v_value_4317_, lean_object* v_FType_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v___x_4324_; lean_object* v___f_4325_; uint8_t v___x_4326_; lean_object* v___x_4327_; 
v___x_4324_ = l_Lean_instInhabitedExpr;
v___f_4325_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4325_, 0, v_recArgInfo_4316_);
lean_closure_set(v___f_4325_, 1, v_FType_4318_);
lean_closure_set(v___f_4325_, 2, v___x_4324_);
lean_closure_set(v___f_4325_, 3, v_recArgInfos_4314_);
lean_closure_set(v___f_4325_, 4, v_positions_4315_);
v___x_4326_ = 0;
v___x_4327_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4317_, v___f_4325_, v___x_4326_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4328_, lean_object* v_positions_4329_, lean_object* v_recArgInfo_4330_, lean_object* v_value_4331_, lean_object* v_FType_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4328_, v_positions_4329_, v_recArgInfo_4330_, v_value_4331_, v_FType_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4339_, lean_object* v_params_4340_, uint8_t v_isIndPred_4341_, lean_object* v_brecOnUniv_4342_, lean_object* v_levels_4343_, lean_object* v_idx_4344_){
_start:
{
lean_object* v_n_4345_; lean_object* v___y_4347_; 
v_n_4345_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4339_, v_idx_4344_);
if (v_isIndPred_4341_ == 0)
{
lean_object* v___x_4350_; 
v___x_4350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4350_, 0, v_brecOnUniv_4342_);
lean_ctor_set(v___x_4350_, 1, v_levels_4343_);
v___y_4347_ = v___x_4350_;
goto v___jp_4346_;
}
else
{
lean_dec(v_brecOnUniv_4342_);
v___y_4347_ = v_levels_4343_;
goto v___jp_4346_;
}
v___jp_4346_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4348_ = l_Lean_Expr_const___override(v_n_4345_, v___y_4347_);
v___x_4349_ = l_Lean_mkAppN(v___x_4348_, v_params_4340_);
return v___x_4349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4351_, lean_object* v_params_4352_, lean_object* v_isIndPred_4353_, lean_object* v_brecOnUniv_4354_, lean_object* v_levels_4355_, lean_object* v_idx_4356_){
_start:
{
uint8_t v_isIndPred_boxed_4357_; lean_object* v_res_4358_; 
v_isIndPred_boxed_4357_ = lean_unbox(v_isIndPred_4353_);
v_res_4358_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4351_, v_params_4352_, v_isIndPred_boxed_4357_, v_brecOnUniv_4354_, v_levels_4355_, v_idx_4356_);
lean_dec(v_idx_4356_);
lean_dec_ref(v_params_4352_);
lean_dec_ref(v_toIndGroupInfo_4351_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4359_, lean_object* v_a_4360_, lean_object* v_n_4361_){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = lean_apply_1(v_brecOnCons_4359_, v_n_4361_);
v___x_4363_ = l_Lean_mkAppN(v___x_4362_, v_a_4360_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4364_, lean_object* v_a_4365_, lean_object* v_n_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4364_, v_a_4365_, v_n_4366_);
lean_dec_ref(v_a_4365_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4368_, lean_object* v_type_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Lean_Meta_getLevel(v_type_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4376_, lean_object* v_type_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4376_, v_type_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec_ref(v_x_4376_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(lean_object* v_inst_4384_, lean_object* v_xs_4385_, size_t v_sz_4386_, size_t v_i_4387_, lean_object* v_bs_4388_){
_start:
{
uint8_t v___x_4389_; 
v___x_4389_ = lean_usize_dec_lt(v_i_4387_, v_sz_4386_);
if (v___x_4389_ == 0)
{
lean_dec(v_inst_4384_);
return v_bs_4388_;
}
else
{
lean_object* v_v_4390_; lean_object* v___x_4391_; lean_object* v_bs_x27_4392_; lean_object* v___x_4393_; size_t v___x_4394_; size_t v___x_4395_; lean_object* v___x_4396_; 
v_v_4390_ = lean_array_uget(v_bs_4388_, v_i_4387_);
v___x_4391_ = lean_unsigned_to_nat(0u);
v_bs_x27_4392_ = lean_array_uset(v_bs_4388_, v_i_4387_, v___x_4391_);
lean_inc(v_inst_4384_);
v___x_4393_ = lean_array_get_borrowed(v_inst_4384_, v_xs_4385_, v_v_4390_);
lean_dec(v_v_4390_);
v___x_4394_ = ((size_t)1ULL);
v___x_4395_ = lean_usize_add(v_i_4387_, v___x_4394_);
lean_inc(v___x_4393_);
v___x_4396_ = lean_array_uset(v_bs_x27_4392_, v_i_4387_, v___x_4393_);
v_i_4387_ = v___x_4395_;
v_bs_4388_ = v___x_4396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg___boxed(lean_object* v_inst_4398_, lean_object* v_xs_4399_, lean_object* v_sz_4400_, lean_object* v_i_4401_, lean_object* v_bs_4402_){
_start:
{
size_t v_sz_boxed_4403_; size_t v_i_boxed_4404_; lean_object* v_res_4405_; 
v_sz_boxed_4403_ = lean_unbox_usize(v_sz_4400_);
lean_dec(v_sz_4400_);
v_i_boxed_4404_ = lean_unbox_usize(v_i_4401_);
lean_dec(v_i_4401_);
v_res_4405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(v_inst_4398_, v_xs_4399_, v_sz_boxed_4403_, v_i_boxed_4404_, v_bs_4402_);
lean_dec_ref(v_xs_4399_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_inst_4406_, lean_object* v_xs_4407_, lean_object* v_f_4408_, lean_object* v_as_4409_, lean_object* v_bs_4410_, lean_object* v_i_4411_, lean_object* v_cs_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v___x_4418_; uint8_t v___x_4419_; 
v___x_4418_ = lean_array_get_size(v_as_4409_);
v___x_4419_ = lean_nat_dec_lt(v_i_4411_, v___x_4418_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; 
lean_dec(v_i_4411_);
lean_dec_ref(v_f_4408_);
lean_dec(v_inst_4406_);
v___x_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4420_, 0, v_cs_4412_);
return v___x_4420_;
}
else
{
lean_object* v___x_4421_; uint8_t v___x_4422_; 
v___x_4421_ = lean_array_get_size(v_bs_4410_);
v___x_4422_ = lean_nat_dec_lt(v_i_4411_, v___x_4421_);
if (v___x_4422_ == 0)
{
lean_object* v___x_4423_; 
lean_dec(v_i_4411_);
lean_dec_ref(v_f_4408_);
lean_dec(v_inst_4406_);
v___x_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4423_, 0, v_cs_4412_);
return v___x_4423_;
}
else
{
lean_object* v_a_4424_; lean_object* v_b_4425_; size_t v_sz_4426_; size_t v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v_a_4424_ = lean_array_fget_borrowed(v_as_4409_, v_i_4411_);
v_b_4425_ = lean_array_fget_borrowed(v_bs_4410_, v_i_4411_);
v_sz_4426_ = lean_array_size(v_b_4425_);
v___x_4427_ = ((size_t)0ULL);
lean_inc(v_b_4425_);
lean_inc(v_inst_4406_);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(v_inst_4406_, v_xs_4407_, v_sz_4426_, v___x_4427_, v_b_4425_);
lean_inc_ref(v_f_4408_);
lean_inc(v___y_4416_);
lean_inc_ref(v___y_4415_);
lean_inc(v___y_4414_);
lean_inc_ref(v___y_4413_);
lean_inc(v_a_4424_);
v___x_4429_ = lean_apply_7(v_f_4408_, v_a_4424_, v___x_4428_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, lean_box(0));
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref(v___x_4429_);
v___x_4431_ = lean_unsigned_to_nat(1u);
v___x_4432_ = lean_nat_add(v_i_4411_, v___x_4431_);
lean_dec(v_i_4411_);
v___x_4433_ = lean_array_push(v_cs_4412_, v_a_4430_);
v_i_4411_ = v___x_4432_;
v_cs_4412_ = v___x_4433_;
goto _start;
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec_ref(v_cs_4412_);
lean_dec(v_i_4411_);
lean_dec_ref(v_f_4408_);
lean_dec(v_inst_4406_);
v_a_4435_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4429_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4429_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_inst_4443_, lean_object* v_xs_4444_, lean_object* v_f_4445_, lean_object* v_as_4446_, lean_object* v_bs_4447_, lean_object* v_i_4448_, lean_object* v_cs_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_inst_4443_, v_xs_4444_, v_f_4445_, v_as_4446_, v_bs_4447_, v_i_4448_, v_cs_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec_ref(v_bs_4447_);
lean_dec_ref(v_as_4446_);
lean_dec_ref(v_xs_4444_);
return v_res_4455_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Array_instInhabited(lean_box(0));
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v___x_4463_; lean_object* v_toApplicative_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4525_; 
v___x_4463_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4464_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4525_ == 0)
{
lean_object* v_unused_4526_; 
v_unused_4526_ = lean_ctor_get(v___x_4463_, 1);
lean_dec(v_unused_4526_);
v___x_4466_ = v___x_4463_;
v_isShared_4467_ = v_isSharedCheck_4525_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_toApplicative_4464_);
lean_dec(v___x_4463_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4525_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v_toFunctor_4468_; lean_object* v_toSeq_4469_; lean_object* v_toSeqLeft_4470_; lean_object* v_toSeqRight_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4523_; 
v_toFunctor_4468_ = lean_ctor_get(v_toApplicative_4464_, 0);
v_toSeq_4469_ = lean_ctor_get(v_toApplicative_4464_, 2);
v_toSeqLeft_4470_ = lean_ctor_get(v_toApplicative_4464_, 3);
v_toSeqRight_4471_ = lean_ctor_get(v_toApplicative_4464_, 4);
v_isSharedCheck_4523_ = !lean_is_exclusive(v_toApplicative_4464_);
if (v_isSharedCheck_4523_ == 0)
{
lean_object* v_unused_4524_; 
v_unused_4524_ = lean_ctor_get(v_toApplicative_4464_, 1);
lean_dec(v_unused_4524_);
v___x_4473_ = v_toApplicative_4464_;
v_isShared_4474_ = v_isSharedCheck_4523_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_toSeqRight_4471_);
lean_inc(v_toSeqLeft_4470_);
lean_inc(v_toSeq_4469_);
lean_inc(v_toFunctor_4468_);
lean_dec(v_toApplicative_4464_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4523_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___f_4475_; lean_object* v___f_4476_; lean_object* v___f_4477_; lean_object* v___f_4478_; lean_object* v___x_4479_; lean_object* v___f_4480_; lean_object* v___f_4481_; lean_object* v___f_4482_; lean_object* v___x_4484_; 
v___f_4475_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4476_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref(v_toFunctor_4468_);
v___f_4477_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4477_, 0, v_toFunctor_4468_);
v___f_4478_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4478_, 0, v_toFunctor_4468_);
v___x_4479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___f_4477_);
lean_ctor_set(v___x_4479_, 1, v___f_4478_);
v___f_4480_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4480_, 0, v_toSeqRight_4471_);
v___f_4481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4481_, 0, v_toSeqLeft_4470_);
v___f_4482_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4482_, 0, v_toSeq_4469_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 4, v___f_4480_);
lean_ctor_set(v___x_4473_, 3, v___f_4481_);
lean_ctor_set(v___x_4473_, 2, v___f_4482_);
lean_ctor_set(v___x_4473_, 1, v___f_4475_);
lean_ctor_set(v___x_4473_, 0, v___x_4479_);
v___x_4484_ = v___x_4473_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4479_);
lean_ctor_set(v_reuseFailAlloc_4522_, 1, v___f_4475_);
lean_ctor_set(v_reuseFailAlloc_4522_, 2, v___f_4482_);
lean_ctor_set(v_reuseFailAlloc_4522_, 3, v___f_4481_);
lean_ctor_set(v_reuseFailAlloc_4522_, 4, v___f_4480_);
v___x_4484_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
lean_object* v___x_4486_; 
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 1, v___f_4476_);
lean_ctor_set(v___x_4466_, 0, v___x_4484_);
v___x_4486_ = v___x_4466_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v___f_4476_);
v___x_4486_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v_toApplicative_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4519_; 
v___x_4487_ = l_StateRefT_x27_instMonad___redArg(v___x_4486_);
v_toApplicative_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4487_, 1);
lean_dec(v_unused_4520_);
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4519_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_toApplicative_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4519_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v_toFunctor_4492_; lean_object* v_toSeq_4493_; lean_object* v_toSeqLeft_4494_; lean_object* v_toSeqRight_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4517_; 
v_toFunctor_4492_ = lean_ctor_get(v_toApplicative_4488_, 0);
v_toSeq_4493_ = lean_ctor_get(v_toApplicative_4488_, 2);
v_toSeqLeft_4494_ = lean_ctor_get(v_toApplicative_4488_, 3);
v_toSeqRight_4495_ = lean_ctor_get(v_toApplicative_4488_, 4);
v_isSharedCheck_4517_ = !lean_is_exclusive(v_toApplicative_4488_);
if (v_isSharedCheck_4517_ == 0)
{
lean_object* v_unused_4518_; 
v_unused_4518_ = lean_ctor_get(v_toApplicative_4488_, 1);
lean_dec(v_unused_4518_);
v___x_4497_ = v_toApplicative_4488_;
v_isShared_4498_ = v_isSharedCheck_4517_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_toSeqRight_4495_);
lean_inc(v_toSeqLeft_4494_);
lean_inc(v_toSeq_4493_);
lean_inc(v_toFunctor_4492_);
lean_dec(v_toApplicative_4488_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4517_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___f_4499_; lean_object* v___f_4500_; lean_object* v___f_4501_; lean_object* v___f_4502_; lean_object* v___x_4503_; lean_object* v___f_4504_; lean_object* v___f_4505_; lean_object* v___f_4506_; lean_object* v___x_4508_; 
v___f_4499_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4500_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4492_);
v___f_4501_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4501_, 0, v_toFunctor_4492_);
v___f_4502_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4502_, 0, v_toFunctor_4492_);
v___x_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___f_4501_);
lean_ctor_set(v___x_4503_, 1, v___f_4502_);
v___f_4504_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4504_, 0, v_toSeqRight_4495_);
v___f_4505_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4505_, 0, v_toSeqLeft_4494_);
v___f_4506_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4506_, 0, v_toSeq_4493_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 4, v___f_4504_);
lean_ctor_set(v___x_4497_, 3, v___f_4505_);
lean_ctor_set(v___x_4497_, 2, v___f_4506_);
lean_ctor_set(v___x_4497_, 1, v___f_4499_);
lean_ctor_set(v___x_4497_, 0, v___x_4503_);
v___x_4508_ = v___x_4497_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4516_, 1, v___f_4499_);
lean_ctor_set(v_reuseFailAlloc_4516_, 2, v___f_4506_);
lean_ctor_set(v_reuseFailAlloc_4516_, 3, v___f_4505_);
lean_ctor_set(v_reuseFailAlloc_4516_, 4, v___f_4504_);
v___x_4508_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4510_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 1, v___f_4500_);
lean_ctor_set(v___x_4490_, 0, v___x_4508_);
v___x_4510_ = v___x_4490_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v___f_4500_);
v___x_4510_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_940__overap_4513_; lean_object* v___x_4514_; 
v___x_4511_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4512_ = l_instInhabitedOfMonad___redArg(v___x_4510_, v___x_4511_);
v___x_940__overap_4513_ = lean_panic_fn(v___x_4512_, v_msg_4457_);
lean_inc(v___y_4461_);
lean_inc_ref(v___y_4460_);
lean_inc(v___y_4459_);
lean_inc_ref(v___y_4458_);
v___x_4514_ = lean_apply_5(v___x_940__overap_4513_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, lean_box(0));
return v___x_4514_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
return v_res_4533_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4537_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4538_ = lean_unsigned_to_nat(2u);
v___x_4539_ = lean_unsigned_to_nat(73u);
v___x_4540_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4541_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4542_ = l_mkPanicMessageWithDecl(v___x_4541_, v___x_4540_, v___x_4539_, v___x_4538_, v___x_4537_);
return v___x_4542_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4544_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4545_ = lean_unsigned_to_nat(2u);
v___x_4546_ = lean_unsigned_to_nat(74u);
v___x_4547_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4548_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4549_ = l_mkPanicMessageWithDecl(v___x_4548_, v___x_4547_, v___x_4546_, v___x_4545_, v___x_4544_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_inst_4552_, lean_object* v_f_4553_, lean_object* v_positions_4554_, lean_object* v_ys_4555_, lean_object* v_xs_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; uint8_t v___x_4564_; 
v___x_4562_ = lean_array_get_size(v_positions_4554_);
v___x_4563_ = lean_array_get_size(v_ys_4555_);
v___x_4564_ = lean_nat_dec_eq(v___x_4562_, v___x_4563_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
lean_dec_ref(v_f_4553_);
lean_dec(v_inst_4552_);
v___x_4565_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4566_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4565_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; 
v___x_4567_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4554_);
v___x_4568_ = lean_array_get_size(v_xs_4556_);
v___x_4569_ = lean_nat_dec_eq(v___x_4567_, v___x_4568_);
lean_dec(v___x_4567_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
lean_dec_ref(v_f_4553_);
lean_dec(v_inst_4552_);
v___x_4570_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4571_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4570_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
return v___x_4571_;
}
else
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4572_ = lean_unsigned_to_nat(0u);
v___x_4573_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4574_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_inst_4552_, v_xs_4556_, v_f_4553_, v_ys_4555_, v_positions_4554_, v___x_4572_, v___x_4573_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
return v___x_4574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_inst_4575_, lean_object* v_f_4576_, lean_object* v_positions_4577_, lean_object* v_ys_4578_, lean_object* v_xs_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_inst_4575_, v_f_4576_, v_positions_4577_, v_ys_4578_, v_xs_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec_ref(v_xs_4579_);
lean_dec_ref(v_ys_4578_);
lean_dec_ref(v_positions_4577_);
return v_res_4585_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4587_ = lean_unsigned_to_nat(0u);
v___x_4588_ = l_Lean_Level_ofNat(v___x_4587_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4589_, lean_object* v_positions_4590_, lean_object* v_motives_4591_, uint8_t v_isIndPred_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v_indGroupInst_4601_; lean_object* v___x_4602_; lean_object* v_brecOnUniv_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4608_; 
v___x_4598_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4599_ = lean_unsigned_to_nat(0u);
v___x_4600_ = lean_array_get_borrowed(v___x_4598_, v_recArgInfos_4589_, v___x_4599_);
v_indGroupInst_4601_ = lean_ctor_get(v___x_4600_, 4);
v___x_4602_ = l_Lean_instInhabitedExpr;
if (v_isIndPred_4592_ == 0)
{
lean_object* v___f_4645_; lean_object* v_motive_4646_; lean_object* v___x_4647_; 
v___f_4645_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v_motive_4646_ = lean_array_get_borrowed(v___x_4602_, v_motives_4591_, v___x_4599_);
lean_inc(v_motive_4646_);
v___x_4647_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4646_, v___f_4645_, v_isIndPred_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_a_4648_);
lean_dec_ref(v___x_4647_);
v_brecOnUniv_4604_ = v_a_4648_;
v___y_4605_ = v_a_4593_;
v___y_4606_ = v_a_4594_;
v___y_4607_ = v_a_4595_;
v___y_4608_ = v_a_4596_;
goto v___jp_4603_;
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4656_; 
v_a_4649_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4651_ = v___x_4647_;
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4647_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4652_ == 0)
{
v___x_4654_ = v___x_4651_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
else
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4604_ = v___x_4657_;
v___y_4605_ = v_a_4593_;
v___y_4606_ = v_a_4594_;
v___y_4607_ = v_a_4595_;
v___y_4608_ = v_a_4596_;
goto v___jp_4603_;
}
v___jp_4603_:
{
lean_object* v_toIndGroupInfo_4609_; lean_object* v_levels_4610_; lean_object* v_params_4611_; lean_object* v___x_4612_; lean_object* v_brecOnCons_4613_; lean_object* v_brecOnAux_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v_toIndGroupInfo_4609_ = lean_ctor_get(v_indGroupInst_4601_, 0);
v_levels_4610_ = lean_ctor_get(v_indGroupInst_4601_, 1);
v_params_4611_ = lean_ctor_get(v_indGroupInst_4601_, 2);
v___x_4612_ = lean_box(v_isIndPred_4592_);
lean_inc(v_levels_4610_);
lean_inc(v_brecOnUniv_4604_);
lean_inc_ref(v_params_4611_);
lean_inc_ref(v_toIndGroupInfo_4609_);
v_brecOnCons_4613_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4613_, 0, v_toIndGroupInfo_4609_);
lean_closure_set(v_brecOnCons_4613_, 1, v_params_4611_);
lean_closure_set(v_brecOnCons_4613_, 2, v___x_4612_);
lean_closure_set(v_brecOnCons_4613_, 3, v_brecOnUniv_4604_);
lean_closure_set(v_brecOnCons_4613_, 4, v_levels_4610_);
lean_inc(v_levels_4610_);
v_brecOnAux_4614_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4609_, v_params_4611_, v_isIndPred_4592_, v_brecOnUniv_4604_, v_levels_4610_, v___x_4599_);
v___x_4615_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4609_);
v___x_4616_ = l_Lean_Meta_inferArgumentTypesN(v___x_4615_, v_brecOnAux_4614_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
lean_inc(v_a_4617_);
lean_dec_ref(v___x_4616_);
v___x_4618_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___closed__0));
v___x_4619_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4602_, v___x_4618_, v_positions_4590_, v_a_4617_, v_motives_4591_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v_a_4617_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4628_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4622_ = v___x_4619_;
v_isShared_4623_ = v_isSharedCheck_4628_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4619_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4628_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___f_4624_; lean_object* v___x_4626_; 
v___f_4624_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4624_, 0, v_brecOnCons_4613_);
lean_closure_set(v___f_4624_, 1, v_a_4620_);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 0, v___f_4624_);
v___x_4626_ = v___x_4622_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___f_4624_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_dec_ref(v_brecOnCons_4613_);
v_a_4629_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4619_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4619_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec_ref(v_brecOnCons_4613_);
v_a_4637_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4616_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4616_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4658_, lean_object* v_positions_4659_, lean_object* v_motives_4660_, lean_object* v_isIndPred_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
uint8_t v_isIndPred_boxed_4667_; lean_object* v_res_4668_; 
v_isIndPred_boxed_4667_ = lean_unbox(v_isIndPred_4661_);
v_res_4668_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4658_, v_positions_4659_, v_motives_4660_, v_isIndPred_boxed_4667_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec_ref(v_motives_4660_);
lean_dec_ref(v_positions_4659_);
lean_dec_ref(v_recArgInfos_4658_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4669_, lean_object* v_msg_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4677_, lean_object* v_msg_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4677_, v_msg_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4685_, lean_object* v_00_u03b1_4686_, lean_object* v_00_u03b2_4687_, lean_object* v_inst_4688_, lean_object* v_f_4689_, lean_object* v_positions_4690_, lean_object* v_ys_4691_, lean_object* v_xs_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_inst_4688_, v_f_4689_, v_positions_4690_, v_ys_4691_, v_xs_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4699_, lean_object* v_00_u03b1_4700_, lean_object* v_00_u03b2_4701_, lean_object* v_inst_4702_, lean_object* v_f_4703_, lean_object* v_positions_4704_, lean_object* v_ys_4705_, lean_object* v_xs_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4699_, v_00_u03b1_4700_, v_00_u03b2_4701_, v_inst_4702_, v_f_4703_, v_positions_4704_, v_ys_4705_, v_xs_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec_ref(v_xs_4706_);
lean_dec_ref(v_ys_4705_);
lean_dec_ref(v_positions_4704_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_00_u03b2_4713_, lean_object* v_inst_4714_, lean_object* v_xs_4715_, size_t v_sz_4716_, size_t v_i_4717_, lean_object* v_bs_4718_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___redArg(v_inst_4714_, v_xs_4715_, v_sz_4716_, v_i_4717_, v_bs_4718_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4720_, lean_object* v_inst_4721_, lean_object* v_xs_4722_, lean_object* v_sz_4723_, lean_object* v_i_4724_, lean_object* v_bs_4725_){
_start:
{
size_t v_sz_boxed_4726_; size_t v_i_boxed_4727_; lean_object* v_res_4728_; 
v_sz_boxed_4726_ = lean_unbox_usize(v_sz_4723_);
lean_dec(v_sz_4723_);
v_i_boxed_4727_ = lean_unbox_usize(v_i_4724_);
lean_dec(v_i_4724_);
v_res_4728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_00_u03b2_4720_, v_inst_4721_, v_xs_4722_, v_sz_boxed_4726_, v_i_boxed_4727_, v_bs_4725_);
lean_dec_ref(v_xs_4722_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4729_, lean_object* v_00_u03b3_4730_, lean_object* v_00_u03b2_4731_, lean_object* v_inst_4732_, lean_object* v_xs_4733_, lean_object* v_f_4734_, lean_object* v_as_4735_, lean_object* v_bs_4736_, lean_object* v_i_4737_, lean_object* v_cs_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_inst_4732_, v_xs_4733_, v_f_4734_, v_as_4735_, v_bs_4736_, v_i_4737_, v_cs_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4745_, lean_object* v_00_u03b3_4746_, lean_object* v_00_u03b2_4747_, lean_object* v_inst_4748_, lean_object* v_xs_4749_, lean_object* v_f_4750_, lean_object* v_as_4751_, lean_object* v_bs_4752_, lean_object* v_i_4753_, lean_object* v_cs_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4745_, v_00_u03b3_4746_, v_00_u03b2_4747_, v_inst_4748_, v_xs_4749_, v_f_4750_, v_as_4751_, v_bs_4752_, v_i_4753_, v_cs_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_);
lean_dec(v___y_4758_);
lean_dec_ref(v___y_4757_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec_ref(v_bs_4752_);
lean_dec_ref(v_as_4751_);
lean_dec_ref(v_xs_4749_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_4761_, lean_object* v_e_4762_){
_start:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = l_Lean_indentD(v_e_4762_);
v___x_4764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4761_);
lean_ctor_set(v___x_4764_, 1, v___x_4763_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_4765_, lean_object* v_x_4766_, lean_object* v_brecOnType_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4765_, v_brecOnType_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_4774_, lean_object* v_x_4775_, lean_object* v_brecOnType_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_4774_, v_x_4775_, v_brecOnType_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec_ref(v_x_4775_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4783_, lean_object* v_as_4784_, size_t v_sz_4785_, size_t v_i_4786_, lean_object* v_b_4787_){
_start:
{
uint8_t v___x_4789_; 
v___x_4789_ = lean_usize_dec_lt(v_i_4786_, v_sz_4785_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; 
lean_dec_ref(v_a_4783_);
v___x_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4790_, 0, v_b_4787_);
return v___x_4790_;
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4792_; size_t v___x_4793_; size_t v___x_4794_; 
v_a_4791_ = lean_array_uget_borrowed(v_as_4784_, v_i_4786_);
lean_inc_ref(v_a_4783_);
v___x_4792_ = lean_array_set(v_b_4787_, v_a_4791_, v_a_4783_);
v___x_4793_ = ((size_t)1ULL);
v___x_4794_ = lean_usize_add(v_i_4786_, v___x_4793_);
v_i_4786_ = v___x_4794_;
v_b_4787_ = v___x_4792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4796_, lean_object* v_as_4797_, lean_object* v_sz_4798_, lean_object* v_i_4799_, lean_object* v_b_4800_, lean_object* v___y_4801_){
_start:
{
size_t v_sz_boxed_4802_; size_t v_i_boxed_4803_; lean_object* v_res_4804_; 
v_sz_boxed_4802_ = lean_unbox_usize(v_sz_4798_);
lean_dec(v_sz_4798_);
v_i_boxed_4803_ = lean_unbox_usize(v_i_4799_);
lean_dec(v_i_4799_);
v_res_4804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4796_, v_as_4797_, v_sz_boxed_4802_, v_i_boxed_4803_, v_b_4800_);
lean_dec_ref(v_as_4797_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4805_, size_t v_sz_4806_, size_t v_i_4807_, lean_object* v_b_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
uint8_t v___x_4814_; 
v___x_4814_ = lean_usize_dec_lt(v_i_4807_, v_sz_4806_);
if (v___x_4814_ == 0)
{
lean_object* v___x_4815_; 
v___x_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4815_, 0, v_b_4808_);
return v___x_4815_;
}
else
{
lean_object* v_snd_4816_; lean_object* v_fst_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4861_; 
v_snd_4816_ = lean_ctor_get(v_b_4808_, 1);
v_fst_4817_ = lean_ctor_get(v_b_4808_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v_b_4808_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4819_ = v_b_4808_;
v_isShared_4820_ = v_isSharedCheck_4861_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_snd_4816_);
lean_inc(v_fst_4817_);
lean_dec(v_b_4808_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4861_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v_array_4821_; lean_object* v_start_4822_; lean_object* v_stop_4823_; uint8_t v___x_4824_; 
v_array_4821_ = lean_ctor_get(v_snd_4816_, 0);
v_start_4822_ = lean_ctor_get(v_snd_4816_, 1);
v_stop_4823_ = lean_ctor_get(v_snd_4816_, 2);
v___x_4824_ = lean_nat_dec_lt(v_start_4822_, v_stop_4823_);
if (v___x_4824_ == 0)
{
lean_object* v___x_4826_; 
if (v_isShared_4820_ == 0)
{
v___x_4826_ = v___x_4819_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_fst_4817_);
lean_ctor_set(v_reuseFailAlloc_4828_, 1, v_snd_4816_);
v___x_4826_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
lean_object* v___x_4827_; 
v___x_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
return v___x_4827_;
}
}
else
{
lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4857_; 
lean_inc(v_stop_4823_);
lean_inc(v_start_4822_);
lean_inc_ref(v_array_4821_);
v_isSharedCheck_4857_ = !lean_is_exclusive(v_snd_4816_);
if (v_isSharedCheck_4857_ == 0)
{
lean_object* v_unused_4858_; lean_object* v_unused_4859_; lean_object* v_unused_4860_; 
v_unused_4858_ = lean_ctor_get(v_snd_4816_, 2);
lean_dec(v_unused_4858_);
v_unused_4859_ = lean_ctor_get(v_snd_4816_, 1);
lean_dec(v_unused_4859_);
v_unused_4860_ = lean_ctor_get(v_snd_4816_, 0);
lean_dec(v_unused_4860_);
v___x_4830_ = v_snd_4816_;
v_isShared_4831_ = v_isSharedCheck_4857_;
goto v_resetjp_4829_;
}
else
{
lean_dec(v_snd_4816_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4857_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v_a_4832_; lean_object* v___x_4833_; size_t v_sz_4834_; size_t v___x_4835_; lean_object* v___x_4836_; 
v_a_4832_ = lean_array_uget_borrowed(v_as_4805_, v_i_4807_);
v___x_4833_ = lean_array_fget_borrowed(v_array_4821_, v_start_4822_);
v_sz_4834_ = lean_array_size(v___x_4833_);
v___x_4835_ = ((size_t)0ULL);
lean_inc(v_a_4832_);
v___x_4836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4832_, v___x_4833_, v_sz_4834_, v___x_4835_, v_fst_4817_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v_a_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4841_; 
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
lean_inc(v_a_4837_);
lean_dec_ref(v___x_4836_);
v___x_4838_ = lean_unsigned_to_nat(1u);
v___x_4839_ = lean_nat_add(v_start_4822_, v___x_4838_);
lean_dec(v_start_4822_);
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 1, v___x_4839_);
v___x_4841_ = v___x_4830_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_array_4821_);
lean_ctor_set(v_reuseFailAlloc_4848_, 1, v___x_4839_);
lean_ctor_set(v_reuseFailAlloc_4848_, 2, v_stop_4823_);
v___x_4841_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
lean_object* v___x_4843_; 
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 1, v___x_4841_);
lean_ctor_set(v___x_4819_, 0, v_a_4837_);
v___x_4843_ = v___x_4819_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4837_);
lean_ctor_set(v_reuseFailAlloc_4847_, 1, v___x_4841_);
v___x_4843_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
size_t v___x_4844_; size_t v___x_4845_; 
v___x_4844_ = ((size_t)1ULL);
v___x_4845_ = lean_usize_add(v_i_4807_, v___x_4844_);
v_i_4807_ = v___x_4845_;
v_b_4808_ = v___x_4843_;
goto _start;
}
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_del_object(v___x_4830_);
lean_dec(v_stop_4823_);
lean_dec(v_start_4822_);
lean_dec_ref(v_array_4821_);
lean_del_object(v___x_4819_);
v_a_4849_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4836_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4836_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4862_, lean_object* v_sz_4863_, lean_object* v_i_4864_, lean_object* v_b_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
size_t v_sz_boxed_4871_; size_t v_i_boxed_4872_; lean_object* v_res_4873_; 
v_sz_boxed_4871_ = lean_unbox_usize(v_sz_4863_);
lean_dec(v_sz_4863_);
v_i_boxed_4872_ = lean_unbox_usize(v_i_4864_);
lean_dec(v_i_4864_);
v_res_4873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4862_, v_sz_boxed_4871_, v_i_boxed_4872_, v_b_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec_ref(v_as_4862_);
return v_res_4873_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4876_ = l_Lean_stringToMessageData(v___x_4875_);
return v___x_4876_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___f_4878_; 
v___x_4877_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4878_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_4878_, 0, v___x_4877_);
return v___f_4878_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4880_ = l_Lean_Expr_sort___override(v___x_4879_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4881_, lean_object* v_positions_4882_, lean_object* v_brecOnConst_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_){
_start:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v_recArgInfo_4891_; lean_object* v_indicesPos_4892_; lean_object* v_indIdx_4893_; lean_object* v_brecOn_4894_; lean_object* v___f_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4889_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4890_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4891_ = lean_array_get_borrowed(v___x_4889_, v_recArgInfos_4881_, v___x_4890_);
v_indicesPos_4892_ = lean_ctor_get(v_recArgInfo_4891_, 3);
v_indIdx_4893_ = lean_ctor_get(v_recArgInfo_4891_, 5);
lean_inc(v_indIdx_4893_);
v_brecOn_4894_ = lean_apply_1(v_brecOnConst_4883_, v_indIdx_4893_);
v___f_4895_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
lean_inc_ref(v_brecOn_4894_);
v___x_4896_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_4896_, 0, v_brecOn_4894_);
v___x_4897_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4896_, v___f_4895_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v___x_4898_; 
lean_dec_ref(v___x_4897_);
lean_inc(v_a_4887_);
lean_inc_ref(v_a_4886_);
lean_inc(v_a_4885_);
lean_inc_ref(v_a_4884_);
v___x_4898_ = lean_infer_type(v_brecOn_4894_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v_numTypeFormers_4900_; lean_object* v___f_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; uint8_t v___x_4906_; lean_object* v___x_4907_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
lean_inc(v_a_4899_);
lean_dec_ref(v___x_4898_);
v_numTypeFormers_4900_ = lean_array_get_size(v_positions_4882_);
v___f_4901_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4901_, 0, v_numTypeFormers_4900_);
v___x_4902_ = lean_array_get_size(v_indicesPos_4892_);
v___x_4903_ = lean_unsigned_to_nat(1u);
v___x_4904_ = lean_nat_add(v___x_4902_, v___x_4903_);
v___x_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
v___x_4906_ = 0;
v___x_4907_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4899_, v___x_4905_, v___f_4901_, v___x_4906_, v___x_4906_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; size_t v_sz_4914_; size_t v___x_4915_; lean_object* v___x_4916_; 
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
lean_inc(v_a_4908_);
lean_dec_ref(v___x_4907_);
v___x_4909_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4882_);
v___x_4910_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4911_ = lean_mk_array(v___x_4909_, v___x_4910_);
v___x_4912_ = l_Array_toSubarray___redArg(v_positions_4882_, v___x_4890_, v_numTypeFormers_4900_);
v___x_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4911_);
lean_ctor_set(v___x_4913_, 1, v___x_4912_);
v_sz_4914_ = lean_array_size(v_a_4908_);
v___x_4915_ = ((size_t)0ULL);
v___x_4916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4908_, v_sz_4914_, v___x_4915_, v___x_4913_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
lean_dec(v_a_4908_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4925_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4919_ = v___x_4916_;
v_isShared_4920_ = v_isSharedCheck_4925_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4916_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4925_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v_fst_4921_; lean_object* v___x_4923_; 
v_fst_4921_ = lean_ctor_get(v_a_4917_, 0);
lean_inc(v_fst_4921_);
lean_dec(v_a_4917_);
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 0, v_fst_4921_);
v___x_4923_ = v___x_4919_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_fst_4921_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
v_a_4926_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___x_4916_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4916_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4882_);
return v___x_4907_;
}
}
else
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4941_; 
lean_dec_ref(v_positions_4882_);
v_a_4934_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4936_ = v___x_4898_;
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4898_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4939_; 
if (v_isShared_4937_ == 0)
{
v___x_4939_ = v___x_4936_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4934_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
else
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4949_; 
lean_dec_ref(v_brecOn_4894_);
lean_dec_ref(v_positions_4882_);
v_a_4942_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4944_ = v___x_4897_;
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4897_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4947_; 
if (v_isShared_4945_ == 0)
{
v___x_4947_ = v___x_4944_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4950_, lean_object* v_positions_4951_, lean_object* v_brecOnConst_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4950_, v_positions_4951_, v_brecOnConst_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec_ref(v_recArgInfos_4950_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4959_, lean_object* v_as_4960_, size_t v_sz_4961_, size_t v_i_4962_, lean_object* v_b_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v___x_4969_; 
v___x_4969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4959_, v_as_4960_, v_sz_4961_, v_i_4962_, v_b_4963_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4970_, lean_object* v_as_4971_, lean_object* v_sz_4972_, lean_object* v_i_4973_, lean_object* v_b_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
size_t v_sz_boxed_4980_; size_t v_i_boxed_4981_; lean_object* v_res_4982_; 
v_sz_boxed_4980_ = lean_unbox_usize(v_sz_4972_);
lean_dec(v_sz_4972_);
v_i_boxed_4981_ = lean_unbox_usize(v_i_4973_);
lean_dec(v_i_4973_);
v_res_4982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4970_, v_as_4971_, v_sz_boxed_4980_, v_i_boxed_4981_, v_b_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec_ref(v_as_4971_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4983_, lean_object* v_a_4984_){
_start:
{
if (lean_obj_tag(v_a_4983_) == 0)
{
lean_object* v___x_4985_; 
v___x_4985_ = l_List_reverse___redArg(v_a_4984_);
return v___x_4985_;
}
else
{
lean_object* v_head_4986_; lean_object* v_tail_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4998_; 
v_head_4986_ = lean_ctor_get(v_a_4983_, 0);
v_tail_4987_ = lean_ctor_get(v_a_4983_, 1);
v_isSharedCheck_4998_ = !lean_is_exclusive(v_a_4983_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4989_ = v_a_4983_;
v_isShared_4990_ = v_isSharedCheck_4998_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_tail_4987_);
lean_inc(v_head_4986_);
lean_dec(v_a_4983_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4998_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4995_; 
v___x_4991_ = l_Nat_reprFast(v_head_4986_);
v___x_4992_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4991_);
v___x_4993_ = l_Lean_MessageData_ofFormat(v___x_4992_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v_a_4984_);
lean_ctor_set(v___x_4989_, 0, v___x_4993_);
v___x_4995_ = v___x_4989_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4993_);
lean_ctor_set(v_reuseFailAlloc_4997_, 1, v_a_4984_);
v___x_4995_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
v_a_4983_ = v_tail_4987_;
v_a_4984_ = v___x_4995_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
if (lean_obj_tag(v_a_4999_) == 0)
{
lean_object* v___x_5001_; 
v___x_5001_ = l_List_reverse___redArg(v_a_5000_);
return v___x_5001_;
}
else
{
lean_object* v_head_5002_; lean_object* v_tail_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5015_; 
v_head_5002_ = lean_ctor_get(v_a_4999_, 0);
v_tail_5003_ = lean_ctor_get(v_a_4999_, 1);
v_isSharedCheck_5015_ = !lean_is_exclusive(v_a_4999_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5005_ = v_a_4999_;
v_isShared_5006_ = v_isSharedCheck_5015_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_tail_5003_);
lean_inc(v_head_5002_);
lean_dec(v_a_4999_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5015_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5007_ = lean_array_to_list(v_head_5002_);
v___x_5008_ = lean_box(0);
v___x_5009_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_5007_, v___x_5008_);
v___x_5010_ = l_Lean_MessageData_ofList(v___x_5009_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 1, v_a_5000_);
lean_ctor_set(v___x_5005_, 0, v___x_5010_);
v___x_5012_ = v___x_5005_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5014_, 1, v_a_5000_);
v___x_5012_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
v_a_4999_ = v_tail_5003_;
v_a_5000_ = v___x_5012_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_5016_, lean_object* v_v_5017_, lean_object* v_i_5018_){
_start:
{
lean_object* v___x_5019_; uint8_t v___x_5020_; 
v___x_5019_ = lean_array_get_size(v_xs_5016_);
v___x_5020_ = lean_nat_dec_lt(v_i_5018_, v___x_5019_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
lean_dec(v_i_5018_);
v___x_5021_ = lean_box(0);
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; uint8_t v___x_5023_; 
v___x_5022_ = lean_array_fget_borrowed(v_xs_5016_, v_i_5018_);
v___x_5023_ = lean_nat_dec_eq(v___x_5022_, v_v_5017_);
if (v___x_5023_ == 0)
{
lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5024_ = lean_unsigned_to_nat(1u);
v___x_5025_ = lean_nat_add(v_i_5018_, v___x_5024_);
lean_dec(v_i_5018_);
v_i_5018_ = v___x_5025_;
goto _start;
}
else
{
lean_object* v___x_5027_; 
v___x_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5027_, 0, v_i_5018_);
return v___x_5027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_5028_, lean_object* v_v_5029_, lean_object* v_i_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_5028_, v_v_5029_, v_i_5030_);
lean_dec(v_v_5029_);
lean_dec_ref(v_xs_5028_);
return v_res_5031_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_5032_, lean_object* v_v_5033_){
_start:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5034_ = lean_unsigned_to_nat(0u);
v___x_5035_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_5032_, v_v_5033_, v___x_5034_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_5036_, lean_object* v_v_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_5036_, v_v_5037_);
lean_dec(v_v_5037_);
lean_dec_ref(v_xs_5036_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_5042_, lean_object* v_as_5043_, size_t v_sz_5044_, size_t v_i_5045_, lean_object* v_b_5046_){
_start:
{
uint8_t v___x_5047_; 
v___x_5047_ = lean_usize_dec_lt(v_i_5045_, v_sz_5044_);
if (v___x_5047_ == 0)
{
return v_b_5046_;
}
else
{
lean_object* v___x_5048_; lean_object* v_a_5049_; lean_object* v___x_5050_; 
lean_dec_ref(v_b_5046_);
v___x_5048_ = lean_box(0);
v_a_5049_ = lean_array_uget_borrowed(v_as_5043_, v_i_5045_);
v___x_5050_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_5049_, v_fnIdx_5042_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v___x_5051_; size_t v___x_5052_; size_t v___x_5053_; 
v___x_5051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_5052_ = ((size_t)1ULL);
v___x_5053_ = lean_usize_add(v_i_5045_, v___x_5052_);
v_i_5045_ = v___x_5053_;
v_b_5046_ = v___x_5051_;
goto _start;
}
else
{
lean_object* v_val_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5066_; 
v_val_5055_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5057_ = v___x_5050_;
v_isShared_5058_ = v_isSharedCheck_5066_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_val_5055_);
lean_dec(v___x_5050_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5066_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5059_ = lean_array_get_size(v_a_5049_);
v___x_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5059_);
lean_ctor_set(v___x_5060_, 1, v_val_5055_);
if (v_isShared_5058_ == 0)
{
lean_ctor_set(v___x_5057_, 0, v___x_5060_);
v___x_5062_ = v___x_5057_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
v___x_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
lean_ctor_set(v___x_5064_, 1, v___x_5048_);
return v___x_5064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_5067_, lean_object* v_as_5068_, lean_object* v_sz_5069_, lean_object* v_i_5070_, lean_object* v_b_5071_){
_start:
{
size_t v_sz_boxed_5072_; size_t v_i_boxed_5073_; lean_object* v_res_5074_; 
v_sz_boxed_5072_ = lean_unbox_usize(v_sz_5069_);
lean_dec(v_sz_5069_);
v_i_boxed_5073_ = lean_unbox_usize(v_i_5070_);
lean_dec(v_i_5070_);
v_res_5074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5067_, v_as_5068_, v_sz_boxed_5072_, v_i_boxed_5073_, v_b_5071_);
lean_dec_ref(v_as_5068_);
lean_dec(v_fnIdx_5067_);
return v_res_5074_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_5077_ = l_Lean_stringToMessageData(v___x_5076_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_5078_, lean_object* v_positions_5079_, lean_object* v_fnIdx_5080_, lean_object* v_brecOnConst_5081_, lean_object* v_packedFArgs_5082_, lean_object* v_funTypes_5083_, lean_object* v_ys_5084_, lean_object* v___value_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___x_5109_; lean_object* v_fst_5110_; lean_object* v_snd_5111_; lean_object* v___x_5112_; size_t v_sz_5113_; size_t v___x_5114_; lean_object* v___x_5115_; lean_object* v_fst_5116_; 
lean_inc_ref(v_ys_5084_);
lean_inc_ref(v_recArgInfo_5078_);
v___x_5109_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_5078_, v_ys_5084_);
v_fst_5110_ = lean_ctor_get(v___x_5109_, 0);
lean_inc(v_fst_5110_);
v_snd_5111_ = lean_ctor_get(v___x_5109_, 1);
lean_inc(v_snd_5111_);
lean_dec_ref(v___x_5109_);
v___x_5112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5113_ = lean_array_size(v_positions_5079_);
v___x_5114_ = ((size_t)0ULL);
v___x_5115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5080_, v_positions_5079_, v_sz_5113_, v___x_5114_, v___x_5112_);
v_fst_5116_ = lean_ctor_get(v___x_5115_, 0);
lean_inc(v_fst_5116_);
lean_dec_ref(v___x_5115_);
if (lean_obj_tag(v_fst_5116_) == 0)
{
lean_dec(v_snd_5111_);
lean_dec(v_fst_5110_);
lean_dec_ref(v_ys_5084_);
lean_dec_ref(v_brecOnConst_5081_);
lean_dec_ref(v_recArgInfo_5078_);
v___y_5092_ = v___y_5086_;
v___y_5093_ = v___y_5087_;
v___y_5094_ = v___y_5088_;
v___y_5095_ = v___y_5089_;
goto v___jp_5091_;
}
else
{
lean_object* v_val_5117_; 
v_val_5117_ = lean_ctor_get(v_fst_5116_, 0);
lean_inc(v_val_5117_);
lean_dec_ref(v_fst_5116_);
if (lean_obj_tag(v_val_5117_) == 1)
{
lean_object* v_val_5118_; lean_object* v_fst_5119_; lean_object* v_snd_5120_; lean_object* v_indIdx_5121_; lean_object* v_brecOn_5122_; lean_object* v_brecOn_5123_; lean_object* v_brecOn_5124_; lean_object* v___x_5125_; 
lean_dec(v_fnIdx_5080_);
lean_dec_ref(v_positions_5079_);
v_val_5118_ = lean_ctor_get(v_val_5117_, 0);
lean_inc(v_val_5118_);
lean_dec_ref(v_val_5117_);
v_fst_5119_ = lean_ctor_get(v_val_5118_, 0);
lean_inc(v_fst_5119_);
v_snd_5120_ = lean_ctor_get(v_val_5118_, 1);
lean_inc(v_snd_5120_);
lean_dec(v_val_5118_);
v_indIdx_5121_ = lean_ctor_get(v_recArgInfo_5078_, 5);
lean_inc(v_indIdx_5121_);
lean_dec_ref(v_recArgInfo_5078_);
v_brecOn_5122_ = lean_apply_1(v_brecOnConst_5081_, v_indIdx_5121_);
v_brecOn_5123_ = l_Lean_mkAppN(v_brecOn_5122_, v_fst_5110_);
lean_dec(v_fst_5110_);
v_brecOn_5124_ = l_Lean_mkAppN(v_brecOn_5123_, v_packedFArgs_5082_);
v___x_5125_ = l_Lean_Meta_PProdN_projM(v_fst_5119_, v_snd_5120_, v_brecOn_5124_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
lean_dec(v_snd_5120_);
lean_dec(v_fst_5119_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5127_; uint8_t v___x_5128_; uint8_t v___x_5129_; lean_object* v___x_5130_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5126_);
lean_dec_ref(v___x_5125_);
v___x_5127_ = l_Lean_mkAppN(v_a_5126_, v_snd_5111_);
lean_dec(v_snd_5111_);
v___x_5128_ = 1;
v___x_5129_ = 1;
v___x_5130_ = l_Lean_Meta_mkLetFVars(v_funTypes_5083_, v___x_5127_, v___x_5128_, v___x_5128_, v___x_5129_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; uint8_t v___x_5132_; lean_object* v___x_5133_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref(v___x_5130_);
v___x_5132_ = 0;
v___x_5133_ = l_Lean_Meta_mkLambdaFVars(v_ys_5084_, v_a_5131_, v___x_5132_, v___x_5128_, v___x_5132_, v___x_5128_, v___x_5129_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
lean_dec_ref(v_ys_5084_);
return v___x_5133_;
}
else
{
lean_dec_ref(v_ys_5084_);
return v___x_5130_;
}
}
else
{
lean_dec(v_snd_5111_);
lean_dec_ref(v_ys_5084_);
return v___x_5125_;
}
}
else
{
lean_dec(v_val_5117_);
lean_dec(v_snd_5111_);
lean_dec(v_fst_5110_);
lean_dec_ref(v_ys_5084_);
lean_dec_ref(v_brecOnConst_5081_);
lean_dec_ref(v_recArgInfo_5078_);
v___y_5092_ = v___y_5086_;
v___y_5093_ = v___y_5087_;
v___y_5094_ = v___y_5088_;
v___y_5095_ = v___y_5089_;
goto v___jp_5091_;
}
}
v___jp_5091_:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5096_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_5097_ = l_Nat_reprFast(v_fnIdx_5080_);
v___x_5098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5098_, 0, v___x_5097_);
v___x_5099_ = l_Lean_MessageData_ofFormat(v___x_5098_);
v___x_5100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5096_);
lean_ctor_set(v___x_5100_, 1, v___x_5099_);
v___x_5101_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_5102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5100_);
lean_ctor_set(v___x_5102_, 1, v___x_5101_);
v___x_5103_ = lean_array_to_list(v_positions_5079_);
v___x_5104_ = lean_box(0);
v___x_5105_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5103_, v___x_5104_);
v___x_5106_ = l_Lean_MessageData_ofList(v___x_5105_);
v___x_5107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5102_);
lean_ctor_set(v___x_5107_, 1, v___x_5106_);
v___x_5108_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5107_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
return v___x_5108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5134_, lean_object* v_positions_5135_, lean_object* v_fnIdx_5136_, lean_object* v_brecOnConst_5137_, lean_object* v_packedFArgs_5138_, lean_object* v_funTypes_5139_, lean_object* v_ys_5140_, lean_object* v___value_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5134_, v_positions_5135_, v_fnIdx_5136_, v_brecOnConst_5137_, v_packedFArgs_5138_, v_funTypes_5139_, v_ys_5140_, v___value_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec_ref(v___value_5141_);
lean_dec_ref(v_funTypes_5139_);
lean_dec_ref(v_packedFArgs_5138_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5148_, lean_object* v_fnIdx_5149_, lean_object* v_brecOnConst_5150_, lean_object* v_packedFArgs_5151_, lean_object* v_funTypes_5152_, lean_object* v_recArgInfo_5153_, lean_object* v_value_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
lean_object* v___f_5160_; uint8_t v___x_5161_; lean_object* v___x_5162_; 
v___f_5160_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5160_, 0, v_recArgInfo_5153_);
lean_closure_set(v___f_5160_, 1, v_positions_5148_);
lean_closure_set(v___f_5160_, 2, v_fnIdx_5149_);
lean_closure_set(v___f_5160_, 3, v_brecOnConst_5150_);
lean_closure_set(v___f_5160_, 4, v_packedFArgs_5151_);
lean_closure_set(v___f_5160_, 5, v_funTypes_5152_);
v___x_5161_ = 0;
v___x_5162_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5154_, v___f_5160_, v___x_5161_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5163_, lean_object* v_fnIdx_5164_, lean_object* v_brecOnConst_5165_, lean_object* v_packedFArgs_5166_, lean_object* v_funTypes_5167_, lean_object* v_recArgInfo_5168_, lean_object* v_value_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5163_, v_fnIdx_5164_, v_brecOnConst_5165_, v_packedFArgs_5166_, v_funTypes_5167_, v_recArgInfo_5168_, v_value_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
return v_res_5175_;
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
