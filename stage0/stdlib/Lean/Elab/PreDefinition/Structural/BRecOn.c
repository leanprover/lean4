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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
static lean_object* l_Lean_Elab_Structural_toBelow___closed__0;
static lean_once_cell_t l_Lean_Elab_Structural_toBelow___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Structural_toBelow___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object*, lean_object*);
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
lean_dec_ref(v_fn_111_);
lean_dec_ref_known(v_a_110_, 2);
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
v___x_395_ = lean_st_ref_set(v___y_356_, v___x_394_);
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
v___x_1072_ = lean_mk_array(v___y_1065_, v___x_1071_);
v___x_1073_ = lean_array_get_size(v___y_1063_);
v___x_1074_ = l_Array_toSubarray___redArg(v___y_1063_, v___y_1064_, v___x_1073_);
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
v___x_1113_ = l_Subarray_copy___redArg(v___y_1108_);
v___x_1114_ = l_Lean_mkAppN(v_f_1055_, v___x_1113_);
lean_dec_ref(v___x_1113_);
lean_inc_ref(v___x_1114_);
v___x_1115_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1045_, v___x_1114_, v___y_1110_, v___y_1109_, v___y_1106_, v___y_1111_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
lean_inc_ref(v___f_1046_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1110_);
v___x_1117_ = lean_apply_5(v___f_1046_, v___y_1110_, v___y_1109_, v___y_1106_, v___y_1111_, lean_box(0));
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
v___y_1063_ = v_a_1116_;
v___y_1064_ = v___y_1107_;
v___y_1065_ = v___x_1126_;
v___y_1066_ = v___f_1125_;
v___y_1067_ = v___y_1110_;
v___y_1068_ = v___y_1109_;
v___y_1069_ = v___y_1106_;
v___y_1070_ = v___y_1111_;
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
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1110_);
v___x_1142_ = lean_apply_5(v___x_8901__overap_1141_, v___y_1110_, v___y_1109_, v___y_1106_, v___y_1111_, lean_box(0));
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref_known(v___x_1142_, 1);
v___y_1063_ = v_a_1116_;
v___y_1064_ = v___y_1107_;
v___y_1065_ = v___x_1126_;
v___y_1066_ = v___f_1125_;
v___y_1067_ = v___y_1110_;
v___y_1068_ = v___y_1109_;
v___y_1069_ = v___y_1106_;
v___y_1070_ = v___y_1111_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v___x_1126_);
lean_dec_ref(v___f_1125_);
lean_dec(v_a_1116_);
lean_dec(v___y_1107_);
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
lean_dec(v___y_1107_);
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
lean_dec(v___y_1107_);
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
v___y_1106_ = v___y_1172_;
v___y_1107_ = v___x_1174_;
v___y_1108_ = v___x_1175_;
v___y_1109_ = v___y_1171_;
v___y_1110_ = v___y_1170_;
v___y_1111_ = v___y_1173_;
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
v___y_1106_ = v___y_1172_;
v___y_1107_ = v___x_1174_;
v___y_1108_ = v___x_1175_;
v___y_1109_ = v___y_1171_;
v___y_1110_ = v___y_1170_;
v___y_1111_ = v___y_1173_;
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
v___x_1506_ = lean_st_ref_set(v___y_1479_, v___x_1505_);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_e_1614_){
_start:
{
if (lean_obj_tag(v_e_1614_) == 0)
{
uint8_t v___x_1615_; 
v___x_1615_ = 2;
return v___x_1615_;
}
else
{
lean_object* v_a_1616_; uint8_t v___x_1617_; 
v_a_1616_ = lean_ctor_get(v_e_1614_, 0);
v___x_1617_ = l_Lean_Expr_hasSyntheticSorry(v_a_1616_);
if (v___x_1617_ == 0)
{
uint8_t v___x_1618_; 
v___x_1618_ = 0;
return v___x_1618_;
}
else
{
uint8_t v___x_1619_; 
v___x_1619_ = 1;
return v___x_1619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_e_1620_){
_start:
{
uint8_t v_res_1621_; lean_object* v_r_1622_; 
v_res_1621_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_e_1620_);
lean_dec_ref(v_e_1620_);
v_r_1622_ = lean_box(v_res_1621_);
return v_r_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1623_, lean_object* v_opt_1624_){
_start:
{
lean_object* v_name_1625_; lean_object* v_defValue_1626_; lean_object* v_map_1627_; lean_object* v___x_1628_; 
v_name_1625_ = lean_ctor_get(v_opt_1624_, 0);
v_defValue_1626_ = lean_ctor_get(v_opt_1624_, 1);
v_map_1627_ = lean_ctor_get(v_opts_1623_, 0);
v___x_1628_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1627_, v_name_1625_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_inc(v_defValue_1626_);
return v_defValue_1626_;
}
else
{
lean_object* v_val_1629_; 
v_val_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_val_1629_);
lean_dec_ref_known(v___x_1628_, 1);
if (lean_obj_tag(v_val_1629_) == 3)
{
lean_object* v_v_1630_; 
v_v_1630_ = lean_ctor_get(v_val_1629_, 0);
lean_inc(v_v_1630_);
lean_dec_ref_known(v_val_1629_, 1);
return v_v_1630_;
}
else
{
lean_dec(v_val_1629_);
lean_inc(v_defValue_1626_);
return v_defValue_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1631_, lean_object* v_opt_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1631_, v_opt_1632_);
lean_dec_ref(v_opt_1632_);
lean_dec_ref(v_opts_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_a_1636_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v_x_1634_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v_x_1634_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set_tag(v___x_1638_, 1);
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_a_1644_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v_x_1634_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v_x_1634_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 0);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg___boxed(lean_object* v_x_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_x_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(size_t v_sz_1655_, size_t v_i_1656_, lean_object* v_bs_1657_){
_start:
{
uint8_t v___x_1658_; 
v___x_1658_ = lean_usize_dec_lt(v_i_1656_, v_sz_1655_);
if (v___x_1658_ == 0)
{
return v_bs_1657_;
}
else
{
lean_object* v_v_1659_; lean_object* v_msg_1660_; lean_object* v___x_1661_; lean_object* v_bs_x27_1662_; size_t v___x_1663_; size_t v___x_1664_; lean_object* v___x_1665_; 
v_v_1659_ = lean_array_uget_borrowed(v_bs_1657_, v_i_1656_);
v_msg_1660_ = lean_ctor_get(v_v_1659_, 1);
lean_inc_ref(v_msg_1660_);
v___x_1661_ = lean_unsigned_to_nat(0u);
v_bs_x27_1662_ = lean_array_uset(v_bs_1657_, v_i_1656_, v___x_1661_);
v___x_1663_ = ((size_t)1ULL);
v___x_1664_ = lean_usize_add(v_i_1656_, v___x_1663_);
v___x_1665_ = lean_array_uset(v_bs_x27_1662_, v_i_1656_, v_msg_1660_);
v_i_1656_ = v___x_1664_;
v_bs_1657_ = v___x_1665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_1667_, lean_object* v_i_1668_, lean_object* v_bs_1669_){
_start:
{
size_t v_sz_boxed_1670_; size_t v_i_boxed_1671_; lean_object* v_res_1672_; 
v_sz_boxed_1670_ = lean_unbox_usize(v_sz_1667_);
lean_dec(v_sz_1667_);
v_i_boxed_1671_ = lean_unbox_usize(v_i_1668_);
lean_dec(v_i_1668_);
v_res_1672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(v_sz_boxed_1670_, v_i_boxed_1671_, v_bs_1669_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_oldTraces_1673_, lean_object* v_data_1674_, lean_object* v_ref_1675_, lean_object* v_msg_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_fileName_1682_; lean_object* v_fileMap_1683_; lean_object* v_options_1684_; lean_object* v_currRecDepth_1685_; lean_object* v_maxRecDepth_1686_; lean_object* v_ref_1687_; lean_object* v_currNamespace_1688_; lean_object* v_openDecls_1689_; lean_object* v_initHeartbeats_1690_; lean_object* v_maxHeartbeats_1691_; lean_object* v_quotContext_1692_; lean_object* v_currMacroScope_1693_; uint8_t v_diag_1694_; lean_object* v_cancelTk_x3f_1695_; uint8_t v_suppressElabErrors_1696_; lean_object* v_inheritedTraceOptions_1697_; lean_object* v___x_1698_; lean_object* v_traceState_1699_; lean_object* v_traces_1700_; lean_object* v_ref_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; size_t v_sz_1704_; size_t v___x_1705_; lean_object* v___x_1706_; lean_object* v_msg_1707_; lean_object* v___x_1708_; lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1746_; 
v_fileName_1682_ = lean_ctor_get(v___y_1679_, 0);
v_fileMap_1683_ = lean_ctor_get(v___y_1679_, 1);
v_options_1684_ = lean_ctor_get(v___y_1679_, 2);
v_currRecDepth_1685_ = lean_ctor_get(v___y_1679_, 3);
v_maxRecDepth_1686_ = lean_ctor_get(v___y_1679_, 4);
v_ref_1687_ = lean_ctor_get(v___y_1679_, 5);
v_currNamespace_1688_ = lean_ctor_get(v___y_1679_, 6);
v_openDecls_1689_ = lean_ctor_get(v___y_1679_, 7);
v_initHeartbeats_1690_ = lean_ctor_get(v___y_1679_, 8);
v_maxHeartbeats_1691_ = lean_ctor_get(v___y_1679_, 9);
v_quotContext_1692_ = lean_ctor_get(v___y_1679_, 10);
v_currMacroScope_1693_ = lean_ctor_get(v___y_1679_, 11);
v_diag_1694_ = lean_ctor_get_uint8(v___y_1679_, sizeof(void*)*14);
v_cancelTk_x3f_1695_ = lean_ctor_get(v___y_1679_, 12);
v_suppressElabErrors_1696_ = lean_ctor_get_uint8(v___y_1679_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1697_ = lean_ctor_get(v___y_1679_, 13);
v___x_1698_ = lean_st_ref_get(v___y_1680_);
v_traceState_1699_ = lean_ctor_get(v___x_1698_, 4);
lean_inc_ref(v_traceState_1699_);
lean_dec(v___x_1698_);
v_traces_1700_ = lean_ctor_get(v_traceState_1699_, 0);
lean_inc_ref(v_traces_1700_);
lean_dec_ref(v_traceState_1699_);
v_ref_1701_ = l_Lean_replaceRef(v_ref_1675_, v_ref_1687_);
lean_inc_ref(v_inheritedTraceOptions_1697_);
lean_inc(v_cancelTk_x3f_1695_);
lean_inc(v_currMacroScope_1693_);
lean_inc(v_quotContext_1692_);
lean_inc(v_maxHeartbeats_1691_);
lean_inc(v_initHeartbeats_1690_);
lean_inc(v_openDecls_1689_);
lean_inc(v_currNamespace_1688_);
lean_inc(v_maxRecDepth_1686_);
lean_inc(v_currRecDepth_1685_);
lean_inc_ref(v_options_1684_);
lean_inc_ref(v_fileMap_1683_);
lean_inc_ref(v_fileName_1682_);
v___x_1702_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1702_, 0, v_fileName_1682_);
lean_ctor_set(v___x_1702_, 1, v_fileMap_1683_);
lean_ctor_set(v___x_1702_, 2, v_options_1684_);
lean_ctor_set(v___x_1702_, 3, v_currRecDepth_1685_);
lean_ctor_set(v___x_1702_, 4, v_maxRecDepth_1686_);
lean_ctor_set(v___x_1702_, 5, v_ref_1701_);
lean_ctor_set(v___x_1702_, 6, v_currNamespace_1688_);
lean_ctor_set(v___x_1702_, 7, v_openDecls_1689_);
lean_ctor_set(v___x_1702_, 8, v_initHeartbeats_1690_);
lean_ctor_set(v___x_1702_, 9, v_maxHeartbeats_1691_);
lean_ctor_set(v___x_1702_, 10, v_quotContext_1692_);
lean_ctor_set(v___x_1702_, 11, v_currMacroScope_1693_);
lean_ctor_set(v___x_1702_, 12, v_cancelTk_x3f_1695_);
lean_ctor_set(v___x_1702_, 13, v_inheritedTraceOptions_1697_);
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*14, v_diag_1694_);
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*14 + 1, v_suppressElabErrors_1696_);
v___x_1703_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1700_);
lean_dec_ref(v_traces_1700_);
v_sz_1704_ = lean_array_size(v___x_1703_);
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(v_sz_1704_, v___x_1705_, v___x_1703_);
v_msg_1707_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1707_, 0, v_data_1674_);
lean_ctor_set(v_msg_1707_, 1, v_msg_1676_);
lean_ctor_set(v_msg_1707_, 2, v___x_1706_);
v___x_1708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1707_, v___y_1677_, v___y_1678_, v___x_1702_, v___y_1680_);
lean_dec_ref_known(v___x_1702_, 14);
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1746_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1746_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v_traceState_1714_; lean_object* v_env_1715_; lean_object* v_nextMacroScope_1716_; lean_object* v_ngen_1717_; lean_object* v_auxDeclNGen_1718_; lean_object* v_cache_1719_; lean_object* v_messages_1720_; lean_object* v_infoState_1721_; lean_object* v_snapshotTasks_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1745_; 
v___x_1713_ = lean_st_ref_take(v___y_1680_);
v_traceState_1714_ = lean_ctor_get(v___x_1713_, 4);
v_env_1715_ = lean_ctor_get(v___x_1713_, 0);
v_nextMacroScope_1716_ = lean_ctor_get(v___x_1713_, 1);
v_ngen_1717_ = lean_ctor_get(v___x_1713_, 2);
v_auxDeclNGen_1718_ = lean_ctor_get(v___x_1713_, 3);
v_cache_1719_ = lean_ctor_get(v___x_1713_, 5);
v_messages_1720_ = lean_ctor_get(v___x_1713_, 6);
v_infoState_1721_ = lean_ctor_get(v___x_1713_, 7);
v_snapshotTasks_1722_ = lean_ctor_get(v___x_1713_, 8);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1724_ = v___x_1713_;
v_isShared_1725_ = v_isSharedCheck_1745_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_snapshotTasks_1722_);
lean_inc(v_infoState_1721_);
lean_inc(v_messages_1720_);
lean_inc(v_cache_1719_);
lean_inc(v_traceState_1714_);
lean_inc(v_auxDeclNGen_1718_);
lean_inc(v_ngen_1717_);
lean_inc(v_nextMacroScope_1716_);
lean_inc(v_env_1715_);
lean_dec(v___x_1713_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1745_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
uint64_t v_tid_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1743_; 
v_tid_1726_ = lean_ctor_get_uint64(v_traceState_1714_, sizeof(void*)*1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_traceState_1714_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; 
v_unused_1744_ = lean_ctor_get(v_traceState_1714_, 0);
lean_dec(v_unused_1744_);
v___x_1728_ = v_traceState_1714_;
v_isShared_1729_ = v_isSharedCheck_1743_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v_traceState_1714_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1743_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_ref_1675_);
lean_ctor_set(v___x_1730_, 1, v_a_1709_);
v___x_1731_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1673_, v___x_1730_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1731_);
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1731_);
lean_ctor_set_uint64(v_reuseFailAlloc_1742_, sizeof(void*)*1, v_tid_1726_);
v___x_1733_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v___x_1733_);
v___x_1735_ = v___x_1724_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_env_1715_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_nextMacroScope_1716_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_ngen_1717_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_auxDeclNGen_1718_);
lean_ctor_set(v_reuseFailAlloc_1741_, 4, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1741_, 5, v_cache_1719_);
lean_ctor_set(v_reuseFailAlloc_1741_, 6, v_messages_1720_);
lean_ctor_set(v_reuseFailAlloc_1741_, 7, v_infoState_1721_);
lean_ctor_set(v_reuseFailAlloc_1741_, 8, v_snapshotTasks_1722_);
v___x_1735_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1736_ = lean_st_ref_set(v___y_1680_, v___x_1735_);
v___x_1737_ = lean_box(0);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1737_);
v___x_1739_ = v___x_1711_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_oldTraces_1747_, lean_object* v_data_1748_, lean_object* v_ref_1749_, lean_object* v_msg_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_oldTraces_1747_, v_data_1748_, v_ref_1749_, v_msg_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1763_; double v___x_1764_; 
v___x_1763_ = lean_unsigned_to_nat(1000u);
v___x_1764_ = lean_float_of_nat(v___x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1765_, uint8_t v_collapsed_1766_, lean_object* v_tag_1767_, lean_object* v_opts_1768_, uint8_t v_clsEnabled_1769_, lean_object* v_oldTraces_1770_, lean_object* v_msg_1771_, lean_object* v_resStartStop_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1877_; 
v_fst_1778_ = lean_ctor_get(v_resStartStop_1772_, 0);
v_snd_1779_ = lean_ctor_get(v_resStartStop_1772_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_resStartStop_1772_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1781_ = v_resStartStop_1772_;
v_isShared_1782_ = v_isSharedCheck_1877_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
lean_dec(v_resStartStop_1772_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1877_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v_data_1786_; lean_object* v_fst_1797_; lean_object* v_snd_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1876_; 
v_fst_1797_ = lean_ctor_get(v_snd_1779_, 0);
v_snd_1798_ = lean_ctor_get(v_snd_1779_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_snd_1779_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1800_ = v_snd_1779_;
v_isShared_1801_ = v_isSharedCheck_1876_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snd_1798_);
lean_inc(v_fst_1797_);
lean_dec(v_snd_1779_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1876_;
goto v_resetjp_1799_;
}
v___jp_1783_:
{
lean_object* v___x_1787_; 
lean_inc(v___y_1785_);
v___x_1787_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_oldTraces_1770_, v_data_1786_, v___y_1785_, v___y_1784_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1788_; 
lean_dec_ref_known(v___x_1787_, 1);
v___x_1788_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_fst_1778_);
return v___x_1788_;
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_fst_1778_);
v_a_1789_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1787_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1787_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___y_1805_; lean_object* v_a_1806_; uint8_t v___y_1830_; double v___y_1861_; 
v___x_1802_ = l_Lean_trace_profiler;
v___x_1803_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1768_, v___x_1802_);
if (v___x_1803_ == 0)
{
v___y_1830_ = v___x_1803_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1867_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1768_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; double v___x_1870_; double v___x_1871_; double v___x_1872_; 
v___x_1868_ = l_Lean_trace_profiler_threshold;
v___x_1869_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1768_, v___x_1868_);
v___x_1870_ = lean_float_of_nat(v___x_1869_);
v___x_1871_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4);
v___x_1872_ = lean_float_div(v___x_1870_, v___x_1871_);
v___y_1861_ = v___x_1872_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; double v___x_1875_; 
v___x_1873_ = l_Lean_trace_profiler_threshold;
v___x_1874_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1768_, v___x_1873_);
v___x_1875_ = lean_float_of_nat(v___x_1874_);
v___y_1861_ = v___x_1875_;
goto v___jp_1860_;
}
}
v___jp_1804_:
{
uint8_t v_result_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1812_; 
v_result_1807_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_fst_1778_);
v___x_1808_ = l_Lean_TraceResult_toEmoji(v_result_1807_);
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
v___x_1810_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 7);
lean_ctor_set(v___x_1800_, 1, v___x_1810_);
lean_ctor_set(v___x_1800_, 0, v___x_1809_);
v___x_1812_ = v___x_1800_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v_m_1814_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 7);
lean_ctor_set(v___x_1781_, 1, v_a_1806_);
lean_ctor_set(v___x_1781_, 0, v___x_1812_);
v_m_1814_ = v___x_1781_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_a_1806_);
v_m_1814_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; double v___x_1817_; lean_object* v_data_1818_; 
v___x_1815_ = lean_box(v_result_1807_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
v___x_1817_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1767_);
lean_inc_ref(v___x_1816_);
lean_inc(v_cls_1765_);
v_data_1818_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1818_, 0, v_cls_1765_);
lean_ctor_set(v_data_1818_, 1, v___x_1816_);
lean_ctor_set(v_data_1818_, 2, v_tag_1767_);
lean_ctor_set_float(v_data_1818_, sizeof(void*)*3, v___x_1817_);
lean_ctor_set_float(v_data_1818_, sizeof(void*)*3 + 8, v___x_1817_);
lean_ctor_set_uint8(v_data_1818_, sizeof(void*)*3 + 16, v_collapsed_1766_);
if (v___x_1803_ == 0)
{
lean_dec_ref_known(v___x_1816_, 1);
lean_dec(v_snd_1798_);
lean_dec(v_fst_1797_);
lean_dec_ref(v_tag_1767_);
lean_dec(v_cls_1765_);
v___y_1784_ = v_m_1814_;
v___y_1785_ = v___y_1805_;
v_data_1786_ = v_data_1818_;
goto v___jp_1783_;
}
else
{
lean_object* v_data_1819_; double v___x_1820_; double v___x_1821_; 
lean_dec_ref_known(v_data_1818_, 3);
v_data_1819_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1819_, 0, v_cls_1765_);
lean_ctor_set(v_data_1819_, 1, v___x_1816_);
lean_ctor_set(v_data_1819_, 2, v_tag_1767_);
v___x_1820_ = lean_unbox_float(v_fst_1797_);
lean_dec(v_fst_1797_);
lean_ctor_set_float(v_data_1819_, sizeof(void*)*3, v___x_1820_);
v___x_1821_ = lean_unbox_float(v_snd_1798_);
lean_dec(v_snd_1798_);
lean_ctor_set_float(v_data_1819_, sizeof(void*)*3 + 8, v___x_1821_);
lean_ctor_set_uint8(v_data_1819_, sizeof(void*)*3 + 16, v_collapsed_1766_);
v___y_1784_ = v_m_1814_;
v___y_1785_ = v___y_1805_;
v_data_1786_ = v_data_1819_;
goto v___jp_1783_;
}
}
}
}
v___jp_1824_:
{
lean_object* v_ref_1825_; lean_object* v___x_1826_; 
v_ref_1825_ = lean_ctor_get(v___y_1775_, 5);
lean_inc(v___y_1776_);
lean_inc_ref(v___y_1775_);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1773_);
lean_inc(v_fst_1778_);
v___x_1826_ = lean_apply_6(v_msg_1771_, v_fst_1778_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, lean_box(0));
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___y_1805_ = v_ref_1825_;
v_a_1806_ = v_a_1827_;
goto v___jp_1804_;
}
else
{
lean_object* v___x_1828_; 
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__3);
v___y_1805_ = v_ref_1825_;
v_a_1806_ = v___x_1828_;
goto v___jp_1804_;
}
}
v___jp_1829_:
{
if (v_clsEnabled_1769_ == 0)
{
if (v___y_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v_traceState_1832_; lean_object* v_env_1833_; lean_object* v_nextMacroScope_1834_; lean_object* v_ngen_1835_; lean_object* v_auxDeclNGen_1836_; lean_object* v_cache_1837_; lean_object* v_messages_1838_; lean_object* v_infoState_1839_; lean_object* v_snapshotTasks_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1859_; 
lean_del_object(v___x_1800_);
lean_dec(v_snd_1798_);
lean_dec(v_fst_1797_);
lean_del_object(v___x_1781_);
lean_dec_ref(v_msg_1771_);
lean_dec_ref(v_tag_1767_);
lean_dec(v_cls_1765_);
v___x_1831_ = lean_st_ref_take(v___y_1776_);
v_traceState_1832_ = lean_ctor_get(v___x_1831_, 4);
v_env_1833_ = lean_ctor_get(v___x_1831_, 0);
v_nextMacroScope_1834_ = lean_ctor_get(v___x_1831_, 1);
v_ngen_1835_ = lean_ctor_get(v___x_1831_, 2);
v_auxDeclNGen_1836_ = lean_ctor_get(v___x_1831_, 3);
v_cache_1837_ = lean_ctor_get(v___x_1831_, 5);
v_messages_1838_ = lean_ctor_get(v___x_1831_, 6);
v_infoState_1839_ = lean_ctor_get(v___x_1831_, 7);
v_snapshotTasks_1840_ = lean_ctor_get(v___x_1831_, 8);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1842_ = v___x_1831_;
v_isShared_1843_ = v_isSharedCheck_1859_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_snapshotTasks_1840_);
lean_inc(v_infoState_1839_);
lean_inc(v_messages_1838_);
lean_inc(v_cache_1837_);
lean_inc(v_traceState_1832_);
lean_inc(v_auxDeclNGen_1836_);
lean_inc(v_ngen_1835_);
lean_inc(v_nextMacroScope_1834_);
lean_inc(v_env_1833_);
lean_dec(v___x_1831_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1859_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
uint64_t v_tid_1844_; lean_object* v_traces_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1858_; 
v_tid_1844_ = lean_ctor_get_uint64(v_traceState_1832_, sizeof(void*)*1);
v_traces_1845_ = lean_ctor_get(v_traceState_1832_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_traceState_1832_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1847_ = v_traceState_1832_;
v_isShared_1848_ = v_isSharedCheck_1858_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_traces_1845_);
lean_dec(v_traceState_1832_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1858_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1770_, v_traces_1845_);
lean_dec_ref(v_traces_1845_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1849_);
lean_ctor_set_uint64(v_reuseFailAlloc_1857_, sizeof(void*)*1, v_tid_1844_);
v___x_1851_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 4, v___x_1851_);
v___x_1853_ = v___x_1842_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_env_1833_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_nextMacroScope_1834_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_ngen_1835_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_auxDeclNGen_1836_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1856_, 5, v_cache_1837_);
lean_ctor_set(v_reuseFailAlloc_1856_, 6, v_messages_1838_);
lean_ctor_set(v_reuseFailAlloc_1856_, 7, v_infoState_1839_);
lean_ctor_set(v_reuseFailAlloc_1856_, 8, v_snapshotTasks_1840_);
v___x_1853_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_st_ref_set(v___y_1776_, v___x_1853_);
v___x_1855_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_fst_1778_);
return v___x_1855_;
}
}
}
}
}
else
{
goto v___jp_1824_;
}
}
else
{
goto v___jp_1824_;
}
}
v___jp_1860_:
{
double v___x_1862_; double v___x_1863_; double v___x_1864_; uint8_t v___x_1865_; 
v___x_1862_ = lean_unbox_float(v_snd_1798_);
v___x_1863_ = lean_unbox_float(v_fst_1797_);
v___x_1864_ = lean_float_sub(v___x_1862_, v___x_1863_);
v___x_1865_ = lean_float_decLt(v___y_1861_, v___x_1864_);
v___y_1830_ = v___x_1865_;
goto v___jp_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1878_, lean_object* v_collapsed_1879_, lean_object* v_tag_1880_, lean_object* v_opts_1881_, lean_object* v_clsEnabled_1882_, lean_object* v_oldTraces_1883_, lean_object* v_msg_1884_, lean_object* v_resStartStop_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v_collapsed_boxed_1891_; uint8_t v_clsEnabled_boxed_1892_; lean_object* v_res_1893_; 
v_collapsed_boxed_1891_ = lean_unbox(v_collapsed_1879_);
v_clsEnabled_boxed_1892_ = lean_unbox(v_clsEnabled_1882_);
v_res_1893_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1878_, v_collapsed_boxed_1891_, v_tag_1880_, v_opts_1881_, v_clsEnabled_boxed_1892_, v_oldTraces_1883_, v_msg_1884_, v_resStartStop_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_opts_1881_);
return v_res_1893_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1895_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1896_ = l_Lean_Name_append(v___x_1895_, v___x_1894_);
return v___x_1896_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__1(void){
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
lean_object* v_options_1909_; lean_object* v_inheritedTraceOptions_1910_; uint8_t v_hasTrace_1911_; lean_object* v___x_1912_; lean_object* v___f_1913_; 
v_options_1909_ = lean_ctor_get(v_a_1906_, 2);
v_inheritedTraceOptions_1910_ = lean_ctor_get(v_a_1906_, 13);
v_hasTrace_1911_ = lean_ctor_get_uint8(v_options_1909_, sizeof(void*)*1);
v___x_1912_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1899_);
lean_inc_ref(v_recArg_1903_);
v___f_1913_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1913_, 0, v___x_1912_);
lean_closure_set(v___f_1913_, 1, v_fnIndex_1902_);
lean_closure_set(v___f_1913_, 2, v_recArg_1903_);
lean_closure_set(v___f_1913_, 3, v_below_1899_);
if (v_hasTrace_1911_ == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref(v_recArg_1903_);
v___x_1914_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1899_, v_numIndParams_1900_, v_positions_1901_, v___f_1913_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1914_;
}
else
{
lean_object* v___f_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v_a_1923_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v_a_1938_; 
lean_inc_ref(v_below_1899_);
v___f_1915_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1915_, 0, v_below_1899_);
lean_closure_set(v___f_1915_, 1, v_recArg_1903_);
v___x_1916_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1917_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1918_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1919_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1910_, v_options_1909_, v___x_1918_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = l_Lean_trace_profiler;
v___x_1989_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1909_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
lean_dec_ref(v___f_1915_);
v___x_1990_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1899_, v_numIndParams_1900_, v_positions_1901_, v___f_1913_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1990_;
}
else
{
goto v___jp_1947_;
}
}
else
{
goto v___jp_1947_;
}
v___jp_1920_:
{
lean_object* v___x_1924_; double v___x_1925_; double v___x_1926_; double v___x_1927_; double v___x_1928_; double v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1924_ = lean_io_mono_nanos_now();
v___x_1925_ = lean_float_of_nat(v___y_1921_);
v___x_1926_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__1, &l_Lean_Elab_Structural_toBelow___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___closed__1);
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
v___x_1934_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1916_, v_hasTrace_1911_, v___x_1917_, v_options_1909_, v___x_1919_, v___y_1922_, v___f_1915_, v___x_1933_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1934_;
}
v___jp_1935_:
{
lean_object* v___x_1939_; double v___x_1940_; double v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
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
v___x_1946_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1916_, v_hasTrace_1911_, v___x_1917_, v_options_1909_, v___x_1919_, v___y_1936_, v___f_1915_, v___x_1945_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1946_;
}
v___jp_1947_:
{
lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1948_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1907_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1951_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1909_, v___x_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = lean_io_mono_nanos_now();
v___x_1953_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1899_, v_numIndParams_1900_, v_positions_1901_, v___f_1913_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 1);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v___y_1921_ = v___x_1952_;
v___y_1922_ = v_a_1949_;
v_a_1923_ = v___x_1959_;
goto v___jp_1920_;
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
v_a_1962_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1953_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1953_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 0);
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
v___y_1921_ = v___x_1952_;
v___y_1922_ = v_a_1949_;
v_a_1923_ = v___x_1967_;
goto v___jp_1920_;
}
}
}
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_io_get_num_heartbeats();
v___x_1971_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1899_, v_numIndParams_1900_, v_positions_1901_, v___f_1913_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set_tag(v___x_1974_, 1);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
v___y_1936_ = v_a_1949_;
v___y_1937_ = v___x_1970_;
v_a_1938_ = v___x_1977_;
goto v___jp_1935_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 0);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
v___y_1936_ = v_a_1949_;
v___y_1937_ = v___x_1970_;
v_a_1938_ = v___x_1985_;
goto v___jp_1935_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1991_, lean_object* v_numIndParams_1992_, lean_object* v_positions_1993_, lean_object* v_fnIndex_1994_, lean_object* v_recArg_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_Elab_Structural_toBelow(v_below_1991_, v_numIndParams_1992_, v_positions_1993_, v_fnIndex_1994_, v_recArg_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_00_u03b1_2002_, lean_object* v_x_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_x_2003_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2010_, lean_object* v_x_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_00_u03b1_2010_, v_x_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_2018_, lean_object* v___y_2019_, lean_object* v_b_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc(v___y_2019_);
v___x_2026_ = lean_apply_7(v_k_2018_, v_b_2020_, v___y_2019_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, lean_box(0));
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_2027_, lean_object* v___y_2028_, lean_object* v_b_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_2027_, v___y_2028_, v_b_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2028_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_2036_, uint8_t v_bi_2037_, lean_object* v_type_2038_, lean_object* v_k_2039_, uint8_t v_kind_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___f_2047_; lean_object* v___x_2048_; 
lean_inc(v___y_2041_);
v___f_2047_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2047_, 0, v_k_2039_);
lean_closure_set(v___f_2047_, 1, v___y_2041_);
v___x_2048_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2036_, v_bi_2037_, v_type_2038_, v___f_2047_, v_kind_2040_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2048_) == 0)
{
return v___x_2048_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_2057_, lean_object* v_bi_2058_, lean_object* v_type_2059_, lean_object* v_k_2060_, lean_object* v_kind_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
uint8_t v_bi_boxed_2068_; uint8_t v_kind_boxed_2069_; lean_object* v_res_2070_; 
v_bi_boxed_2068_ = lean_unbox(v_bi_2058_);
v_kind_boxed_2069_ = lean_unbox(v_kind_2061_);
v_res_2070_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2057_, v_bi_boxed_2068_, v_type_2059_, v_k_2060_, v_kind_boxed_2069_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2071_, lean_object* v_name_2072_, uint8_t v_bi_2073_, lean_object* v_type_2074_, lean_object* v_k_2075_, uint8_t v_kind_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2072_, v_bi_2073_, v_type_2074_, v_k_2075_, v_kind_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_name_2085_, lean_object* v_bi_2086_, lean_object* v_type_2087_, lean_object* v_k_2088_, lean_object* v_kind_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v_bi_boxed_2096_; uint8_t v_kind_boxed_2097_; lean_object* v_res_2098_; 
v_bi_boxed_2096_ = lean_unbox(v_bi_2086_);
v_kind_boxed_2097_ = lean_unbox(v_kind_2089_);
v_res_2098_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2084_, v_name_2085_, v_bi_boxed_2096_, v_type_2087_, v_k_2088_, v_kind_boxed_2097_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2099_, lean_object* v___y_2100_, lean_object* v_b_2101_, lean_object* v_c_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
lean_inc(v___y_2106_);
lean_inc_ref(v___y_2105_);
lean_inc(v___y_2104_);
lean_inc_ref(v___y_2103_);
lean_inc(v___y_2100_);
v___x_2108_ = lean_apply_8(v_k_2099_, v_b_2101_, v_c_2102_, v___y_2100_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, lean_box(0));
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2109_, lean_object* v___y_2110_, lean_object* v_b_2111_, lean_object* v_c_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2109_, v___y_2110_, v_b_2111_, v_c_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2110_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2119_, lean_object* v_maxFVars_2120_, lean_object* v_k_2121_, uint8_t v_cleanupAnnotations_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___f_2129_; uint8_t v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_inc(v___y_2123_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2129_, 0, v_k_2121_);
lean_closure_set(v___f_2129_, 1, v___y_2123_);
v___x_2130_ = 1;
v___x_2131_ = 0;
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_maxFVars_2120_);
v___x_2133_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2119_, v___x_2130_, v___x_2131_, v___x_2130_, v___x_2131_, v___x_2132_, v___f_2129_, v_cleanupAnnotations_2122_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec_ref_known(v___x_2132_, 1);
if (lean_obj_tag(v___x_2133_) == 0)
{
return v___x_2133_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2142_, lean_object* v_maxFVars_2143_, lean_object* v_k_2144_, lean_object* v_cleanupAnnotations_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2152_; lean_object* v_res_2153_; 
v_cleanupAnnotations_boxed_2152_ = lean_unbox(v_cleanupAnnotations_2145_);
v_res_2153_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2142_, v_maxFVars_2143_, v_k_2144_, v_cleanupAnnotations_boxed_2152_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2154_, lean_object* v_e_2155_, lean_object* v_maxFVars_2156_, lean_object* v_k_2157_, uint8_t v_cleanupAnnotations_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2155_, v_maxFVars_2156_, v_k_2157_, v_cleanupAnnotations_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2166_, lean_object* v_e_2167_, lean_object* v_maxFVars_2168_, lean_object* v_k_2169_, lean_object* v_cleanupAnnotations_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2177_; lean_object* v_res_2178_; 
v_cleanupAnnotations_boxed_2177_ = lean_unbox(v_cleanupAnnotations_2170_);
v_res_2178_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2166_, v_e_2167_, v_maxFVars_2168_, v_k_2169_, v_cleanupAnnotations_boxed_2177_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2179_, lean_object* v_msg_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_ref_2186_; lean_object* v___x_2187_; lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2232_; 
v_ref_2186_ = lean_ctor_get(v___y_2183_, 5);
v___x_2187_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2232_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2232_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v_traceState_2193_; lean_object* v_env_2194_; lean_object* v_nextMacroScope_2195_; lean_object* v_ngen_2196_; lean_object* v_auxDeclNGen_2197_; lean_object* v_cache_2198_; lean_object* v_messages_2199_; lean_object* v_infoState_2200_; lean_object* v_snapshotTasks_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2231_; 
v___x_2192_ = lean_st_ref_take(v___y_2184_);
v_traceState_2193_ = lean_ctor_get(v___x_2192_, 4);
v_env_2194_ = lean_ctor_get(v___x_2192_, 0);
v_nextMacroScope_2195_ = lean_ctor_get(v___x_2192_, 1);
v_ngen_2196_ = lean_ctor_get(v___x_2192_, 2);
v_auxDeclNGen_2197_ = lean_ctor_get(v___x_2192_, 3);
v_cache_2198_ = lean_ctor_get(v___x_2192_, 5);
v_messages_2199_ = lean_ctor_get(v___x_2192_, 6);
v_infoState_2200_ = lean_ctor_get(v___x_2192_, 7);
v_snapshotTasks_2201_ = lean_ctor_get(v___x_2192_, 8);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2203_ = v___x_2192_;
v_isShared_2204_ = v_isSharedCheck_2231_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_snapshotTasks_2201_);
lean_inc(v_infoState_2200_);
lean_inc(v_messages_2199_);
lean_inc(v_cache_2198_);
lean_inc(v_traceState_2193_);
lean_inc(v_auxDeclNGen_2197_);
lean_inc(v_ngen_2196_);
lean_inc(v_nextMacroScope_2195_);
lean_inc(v_env_2194_);
lean_dec(v___x_2192_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2231_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
uint64_t v_tid_2205_; lean_object* v_traces_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2230_; 
v_tid_2205_ = lean_ctor_get_uint64(v_traceState_2193_, sizeof(void*)*1);
v_traces_2206_ = lean_ctor_get(v_traceState_2193_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_traceState_2193_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2208_ = v_traceState_2193_;
v_isShared_2209_ = v_isSharedCheck_2230_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_traces_2206_);
lean_dec(v_traceState_2193_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2230_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; double v___x_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2212_ = 0;
v___x_2213_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2214_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2214_, 0, v_cls_2179_);
lean_ctor_set(v___x_2214_, 1, v___x_2210_);
lean_ctor_set(v___x_2214_, 2, v___x_2213_);
lean_ctor_set_float(v___x_2214_, sizeof(void*)*3, v___x_2211_);
lean_ctor_set_float(v___x_2214_, sizeof(void*)*3 + 8, v___x_2211_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*3 + 16, v___x_2212_);
v___x_2215_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2216_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v_a_2188_);
lean_ctor_set(v___x_2216_, 2, v___x_2215_);
lean_inc(v_ref_2186_);
v___x_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2217_, 0, v_ref_2186_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = l_Lean_PersistentArray_push___redArg(v_traces_2206_, v___x_2217_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2218_);
v___x_2220_ = v___x_2208_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2218_);
lean_ctor_set_uint64(v_reuseFailAlloc_2229_, sizeof(void*)*1, v_tid_2205_);
v___x_2220_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2222_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 4, v___x_2220_);
v___x_2222_ = v___x_2203_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_env_2194_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_nextMacroScope_2195_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_ngen_2196_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_auxDeclNGen_2197_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2228_, 5, v_cache_2198_);
lean_ctor_set(v_reuseFailAlloc_2228_, 6, v_messages_2199_);
lean_ctor_set(v_reuseFailAlloc_2228_, 7, v_infoState_2200_);
lean_ctor_set(v_reuseFailAlloc_2228_, 8, v_snapshotTasks_2201_);
v___x_2222_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2223_ = lean_st_ref_set(v___y_2184_, v___x_2222_);
v___x_2224_ = lean_box(0);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2224_);
v___x_2226_ = v___x_2190_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2233_, lean_object* v_msg_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2233_, v_msg_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2241_, lean_object* v_as_2242_, size_t v_i_2243_, size_t v_stop_2244_){
_start:
{
uint8_t v___x_2245_; 
v___x_2245_ = lean_usize_dec_eq(v_i_2243_, v_stop_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v_fnName_2247_; lean_object* v_recArgPos_2248_; uint8_t v___x_2249_; 
v___x_2246_ = lean_array_uget_borrowed(v_as_2242_, v_i_2243_);
v_fnName_2247_ = lean_ctor_get(v___x_2246_, 0);
v_recArgPos_2248_ = lean_ctor_get(v___x_2246_, 2);
lean_inc(v_recArgPos_2248_);
lean_inc(v_fnName_2247_);
v___x_2249_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2247_, v_recArgPos_2248_, v_e_2241_);
if (v___x_2249_ == 0)
{
size_t v___x_2250_; size_t v___x_2251_; 
v___x_2250_ = ((size_t)1ULL);
v___x_2251_ = lean_usize_add(v_i_2243_, v___x_2250_);
v_i_2243_ = v___x_2251_;
goto _start;
}
else
{
return v___x_2249_;
}
}
else
{
uint8_t v___x_2253_; 
v___x_2253_ = 0;
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2254_, lean_object* v_as_2255_, lean_object* v_i_2256_, lean_object* v_stop_2257_){
_start:
{
size_t v_i_boxed_2258_; size_t v_stop_boxed_2259_; uint8_t v_res_2260_; lean_object* v_r_2261_; 
v_i_boxed_2258_ = lean_unbox_usize(v_i_2256_);
lean_dec(v_i_2256_);
v_stop_boxed_2259_ = lean_unbox_usize(v_stop_2257_);
lean_dec(v_stop_2257_);
v_res_2260_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2254_, v_as_2255_, v_i_boxed_2258_, v_stop_boxed_2259_);
lean_dec_ref(v_as_2255_);
lean_dec_ref(v_e_2254_);
v_r_2261_ = lean_box(v_res_2260_);
return v_r_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2262_, lean_object* v_____do__lift_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_options_2270_; uint8_t v_hasTrace_2271_; 
v_options_2270_ = lean_ctor_get(v___y_2267_, 2);
v_hasTrace_2271_ = lean_ctor_get_uint8(v_options_2270_, sizeof(void*)*1);
if (v_hasTrace_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v___x_2262_);
v___x_2272_ = lean_box(v_hasTrace_2271_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2274_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2275_ = l_Lean_Name_append(v___x_2274_, v___x_2262_);
v___x_2276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2263_, v_options_2270_, v___x_2275_);
lean_dec(v___x_2275_);
v___x_2277_ = lean_box(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2279_, lean_object* v_____do__lift_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2279_, v_____do__lift_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v_____do__lift_2280_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; lean_object* v_env_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2291_ = lean_st_ref_get(v___y_2289_);
v_env_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc_ref(v_env_2292_);
lean_dec(v___x_2291_);
v___x_2293_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2292_, v_declName_2288_);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2295_, v___y_2296_);
lean_dec(v___y_2296_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v_toApplicative_2307_; lean_object* v_toFunctor_2308_; lean_object* v_toSeq_2309_; lean_object* v_toSeqLeft_2310_; lean_object* v_toSeqRight_2311_; lean_object* v___f_2312_; lean_object* v___f_2313_; lean_object* v___f_2314_; lean_object* v___f_2315_; lean_object* v___x_2316_; lean_object* v___f_2317_; lean_object* v___f_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_toApplicative_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2355_; 
v___x_2306_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2307_ = lean_ctor_get(v___x_2306_, 0);
v_toFunctor_2308_ = lean_ctor_get(v_toApplicative_2307_, 0);
v_toSeq_2309_ = lean_ctor_get(v_toApplicative_2307_, 2);
v_toSeqLeft_2310_ = lean_ctor_get(v_toApplicative_2307_, 3);
v_toSeqRight_2311_ = lean_ctor_get(v_toApplicative_2307_, 4);
v___f_2312_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2313_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2308_, 2);
v___f_2314_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2314_, 0, v_toFunctor_2308_);
v___f_2315_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2315_, 0, v_toFunctor_2308_);
v___x_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___f_2314_);
lean_ctor_set(v___x_2316_, 1, v___f_2315_);
lean_inc(v_toSeqRight_2311_);
v___f_2317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2317_, 0, v_toSeqRight_2311_);
lean_inc(v_toSeqLeft_2310_);
v___f_2318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2318_, 0, v_toSeqLeft_2310_);
lean_inc(v_toSeq_2309_);
v___f_2319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2319_, 0, v_toSeq_2309_);
v___x_2320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2316_);
lean_ctor_set(v___x_2320_, 1, v___f_2312_);
lean_ctor_set(v___x_2320_, 2, v___f_2319_);
lean_ctor_set(v___x_2320_, 3, v___f_2318_);
lean_ctor_set(v___x_2320_, 4, v___f_2317_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v___f_2313_);
v___x_2322_ = l_StateRefT_x27_instMonad___redArg(v___x_2321_);
v_toApplicative_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; 
v_unused_2356_ = lean_ctor_get(v___x_2322_, 1);
lean_dec(v_unused_2356_);
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2355_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_toApplicative_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2355_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_toFunctor_2327_; lean_object* v_toSeq_2328_; lean_object* v_toSeqLeft_2329_; lean_object* v_toSeqRight_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2353_; 
v_toFunctor_2327_ = lean_ctor_get(v_toApplicative_2323_, 0);
v_toSeq_2328_ = lean_ctor_get(v_toApplicative_2323_, 2);
v_toSeqLeft_2329_ = lean_ctor_get(v_toApplicative_2323_, 3);
v_toSeqRight_2330_ = lean_ctor_get(v_toApplicative_2323_, 4);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_toApplicative_2323_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v_toApplicative_2323_, 1);
lean_dec(v_unused_2354_);
v___x_2332_ = v_toApplicative_2323_;
v_isShared_2333_ = v_isSharedCheck_2353_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_toSeqRight_2330_);
lean_inc(v_toSeqLeft_2329_);
lean_inc(v_toSeq_2328_);
lean_inc(v_toFunctor_2327_);
lean_dec(v_toApplicative_2323_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2353_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___f_2334_; lean_object* v___f_2335_; lean_object* v___f_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; lean_object* v___f_2339_; lean_object* v___f_2340_; lean_object* v___f_2341_; lean_object* v___x_2343_; 
v___f_2334_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2335_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2327_);
v___f_2336_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2336_, 0, v_toFunctor_2327_);
v___f_2337_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2337_, 0, v_toFunctor_2327_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___f_2336_);
lean_ctor_set(v___x_2338_, 1, v___f_2337_);
v___f_2339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2339_, 0, v_toSeqRight_2330_);
v___f_2340_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2340_, 0, v_toSeqLeft_2329_);
v___f_2341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2341_, 0, v_toSeq_2328_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 4, v___f_2339_);
lean_ctor_set(v___x_2332_, 3, v___f_2340_);
lean_ctor_set(v___x_2332_, 2, v___f_2341_);
lean_ctor_set(v___x_2332_, 1, v___f_2334_);
lean_ctor_set(v___x_2332_, 0, v___x_2338_);
v___x_2343_ = v___x_2332_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___f_2334_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v___f_2341_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v___f_2340_);
lean_ctor_set(v_reuseFailAlloc_2352_, 4, v___f_2339_);
v___x_2343_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v___f_2335_);
lean_ctor_set(v___x_2325_, 0, v___x_2343_);
v___x_2345_ = v___x_2325_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___f_2335_);
v___x_2345_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_27612__overap_2349_; lean_object* v___x_2350_; 
v___x_2346_ = l_StateRefT_x27_instMonad___redArg(v___x_2345_);
v___x_2347_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2348_ = l_instInhabitedOfMonad___redArg(v___x_2346_, v___x_2347_);
v___x_27612__overap_2349_ = lean_panic_fn_borrowed(v___x_2348_, v_msg_2299_);
lean_dec(v___x_2348_);
lean_inc(v___y_2304_);
lean_inc_ref(v___y_2303_);
lean_inc(v___y_2302_);
lean_inc_ref(v___y_2301_);
lean_inc(v___y_2300_);
v___x_2350_ = lean_apply_6(v___x_27612__overap_2349_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, lean_box(0));
return v___x_2350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
return v_res_2364_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
lean_ctor_set(v___x_2370_, 2, v___x_2369_);
lean_ctor_set(v___x_2370_, 3, v___x_2369_);
lean_ctor_set(v___x_2370_, 4, v___x_2368_);
lean_ctor_set(v___x_2370_, 5, v___x_2368_);
lean_ctor_set(v___x_2370_, 6, v___x_2368_);
lean_ctor_set(v___x_2370_, 7, v___x_2368_);
lean_ctor_set(v___x_2370_, 8, v___x_2368_);
lean_ctor_set(v___x_2370_, 9, v___x_2368_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = lean_unsigned_to_nat(32u);
v___x_2372_ = lean_mk_empty_array_with_capacity(v___x_2371_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2374_ = ((size_t)5ULL);
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = lean_unsigned_to_nat(32u);
v___x_2377_ = lean_mk_empty_array_with_capacity(v___x_2376_);
v___x_2378_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2379_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v___x_2377_);
lean_ctor_set(v___x_2379_, 2, v___x_2375_);
lean_ctor_set(v___x_2379_, 3, v___x_2375_);
lean_ctor_set_usize(v___x_2379_, 4, v___x_2374_);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2380_ = lean_box(1);
v___x_2381_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2382_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v___x_2381_);
lean_ctor_set(v___x_2383_, 2, v___x_2380_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2389_ = l_Lean_stringToMessageData(v___x_2388_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2401_ = l_Lean_stringToMessageData(v___x_2400_);
return v___x_2401_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2404_ = l_Lean_stringToMessageData(v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2405_, lean_object* v_declHint_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; lean_object* v_env_2410_; uint8_t v___x_2411_; 
v___x_2409_ = lean_st_ref_get(v___y_2407_);
v_env_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc_ref(v_env_2410_);
lean_dec(v___x_2409_);
v___x_2411_ = l_Lean_Name_isAnonymous(v_declHint_2406_);
if (v___x_2411_ == 0)
{
uint8_t v_isExporting_2412_; 
v_isExporting_2412_ = lean_ctor_get_uint8(v_env_2410_, sizeof(void*)*8);
if (v_isExporting_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec_ref(v_env_2410_);
lean_dec(v_declHint_2406_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_msg_2405_);
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; uint8_t v___x_2415_; 
lean_inc_ref(v_env_2410_);
v___x_2414_ = l_Lean_Environment_setExporting(v_env_2410_, v___x_2411_);
lean_inc(v_declHint_2406_);
lean_inc_ref(v___x_2414_);
v___x_2415_ = l_Lean_Environment_contains(v___x_2414_, v_declHint_2406_, v_isExporting_2412_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; 
lean_dec_ref(v___x_2414_);
lean_dec_ref(v_env_2410_);
lean_dec(v_declHint_2406_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_msg_2405_);
return v___x_2416_;
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v_c_2422_; lean_object* v___x_2423_; 
v___x_2417_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2418_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2419_ = l_Lean_Options_empty;
v___x_2420_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2414_);
lean_ctor_set(v___x_2420_, 1, v___x_2417_);
lean_ctor_set(v___x_2420_, 2, v___x_2418_);
lean_ctor_set(v___x_2420_, 3, v___x_2419_);
lean_inc(v_declHint_2406_);
v___x_2421_ = l_Lean_MessageData_ofConstName(v_declHint_2406_, v___x_2411_);
v_c_2422_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2422_, 0, v___x_2420_);
lean_ctor_set(v_c_2422_, 1, v___x_2421_);
v___x_2423_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2410_, v_declHint_2406_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec_ref(v_env_2410_);
lean_dec(v_declHint_2406_);
v___x_2424_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v_c_2422_);
v___x_2426_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = l_Lean_MessageData_note(v___x_2427_);
v___x_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_msg_2405_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
else
{
lean_object* v_val_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2466_; 
v_val_2431_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2433_ = v___x_2423_;
v_isShared_2434_ = v_isSharedCheck_2466_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_val_2431_);
lean_dec(v___x_2423_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2466_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_mod_2438_; uint8_t v___x_2439_; 
v___x_2435_ = lean_box(0);
v___x_2436_ = l_Lean_Environment_header(v_env_2410_);
lean_dec_ref(v_env_2410_);
v___x_2437_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2436_);
v_mod_2438_ = lean_array_get(v___x_2435_, v___x_2437_, v_val_2431_);
lean_dec(v_val_2431_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = l_Lean_isPrivateName(v_declHint_2406_);
lean_dec(v_declHint_2406_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v_c_2422_);
v___x_2442_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = l_Lean_MessageData_ofName(v_mod_2438_);
v___x_2445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = l_Lean_MessageData_note(v___x_2447_);
v___x_2449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2449_, 0, v_msg_2405_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set_tag(v___x_2433_, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2449_);
v___x_2451_ = v___x_2433_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
lean_ctor_set(v___x_2454_, 1, v_c_2422_);
v___x_2455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Lean_MessageData_ofName(v_mod_2438_);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = l_Lean_MessageData_note(v___x_2460_);
v___x_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_msg_2405_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set_tag(v___x_2433_, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2462_);
v___x_2464_ = v___x_2433_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2467_; 
lean_dec_ref(v_env_2410_);
lean_dec(v_declHint_2406_);
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_msg_2405_);
return v___x_2467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2468_, lean_object* v_declHint_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2468_, v_declHint_2469_, v___y_2470_);
lean_dec(v___y_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2473_, lean_object* v_declHint_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2491_; 
v___x_2481_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2473_, v_declHint_2474_, v___y_2479_);
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2491_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2491_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2486_ = l_Lean_unknownIdentifierMessageTag;
v___x_2487_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v_a_2482_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2487_);
v___x_2489_ = v___x_2484_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2492_, lean_object* v_declHint_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2492_, v_declHint_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_ref_2507_; lean_object* v___x_2508_; lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2517_; 
v_ref_2507_ = lean_ctor_get(v___y_2504_, 5);
v___x_2508_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2517_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2517_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_inc(v_ref_2507_);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v_ref_2507_);
lean_ctor_set(v___x_2513_, 1, v_a_2509_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 1);
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2515_ = v___x_2511_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2525_, lean_object* v_msg_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_fileName_2533_; lean_object* v_fileMap_2534_; lean_object* v_options_2535_; lean_object* v_currRecDepth_2536_; lean_object* v_maxRecDepth_2537_; lean_object* v_ref_2538_; lean_object* v_currNamespace_2539_; lean_object* v_openDecls_2540_; lean_object* v_initHeartbeats_2541_; lean_object* v_maxHeartbeats_2542_; lean_object* v_quotContext_2543_; lean_object* v_currMacroScope_2544_; uint8_t v_diag_2545_; lean_object* v_cancelTk_x3f_2546_; uint8_t v_suppressElabErrors_2547_; lean_object* v_inheritedTraceOptions_2548_; lean_object* v_ref_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_fileName_2533_ = lean_ctor_get(v___y_2530_, 0);
v_fileMap_2534_ = lean_ctor_get(v___y_2530_, 1);
v_options_2535_ = lean_ctor_get(v___y_2530_, 2);
v_currRecDepth_2536_ = lean_ctor_get(v___y_2530_, 3);
v_maxRecDepth_2537_ = lean_ctor_get(v___y_2530_, 4);
v_ref_2538_ = lean_ctor_get(v___y_2530_, 5);
v_currNamespace_2539_ = lean_ctor_get(v___y_2530_, 6);
v_openDecls_2540_ = lean_ctor_get(v___y_2530_, 7);
v_initHeartbeats_2541_ = lean_ctor_get(v___y_2530_, 8);
v_maxHeartbeats_2542_ = lean_ctor_get(v___y_2530_, 9);
v_quotContext_2543_ = lean_ctor_get(v___y_2530_, 10);
v_currMacroScope_2544_ = lean_ctor_get(v___y_2530_, 11);
v_diag_2545_ = lean_ctor_get_uint8(v___y_2530_, sizeof(void*)*14);
v_cancelTk_x3f_2546_ = lean_ctor_get(v___y_2530_, 12);
v_suppressElabErrors_2547_ = lean_ctor_get_uint8(v___y_2530_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v___y_2530_, 13);
v_ref_2549_ = l_Lean_replaceRef(v_ref_2525_, v_ref_2538_);
lean_inc_ref(v_inheritedTraceOptions_2548_);
lean_inc(v_cancelTk_x3f_2546_);
lean_inc(v_currMacroScope_2544_);
lean_inc(v_quotContext_2543_);
lean_inc(v_maxHeartbeats_2542_);
lean_inc(v_initHeartbeats_2541_);
lean_inc(v_openDecls_2540_);
lean_inc(v_currNamespace_2539_);
lean_inc(v_maxRecDepth_2537_);
lean_inc(v_currRecDepth_2536_);
lean_inc_ref(v_options_2535_);
lean_inc_ref(v_fileMap_2534_);
lean_inc_ref(v_fileName_2533_);
v___x_2550_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2550_, 0, v_fileName_2533_);
lean_ctor_set(v___x_2550_, 1, v_fileMap_2534_);
lean_ctor_set(v___x_2550_, 2, v_options_2535_);
lean_ctor_set(v___x_2550_, 3, v_currRecDepth_2536_);
lean_ctor_set(v___x_2550_, 4, v_maxRecDepth_2537_);
lean_ctor_set(v___x_2550_, 5, v_ref_2549_);
lean_ctor_set(v___x_2550_, 6, v_currNamespace_2539_);
lean_ctor_set(v___x_2550_, 7, v_openDecls_2540_);
lean_ctor_set(v___x_2550_, 8, v_initHeartbeats_2541_);
lean_ctor_set(v___x_2550_, 9, v_maxHeartbeats_2542_);
lean_ctor_set(v___x_2550_, 10, v_quotContext_2543_);
lean_ctor_set(v___x_2550_, 11, v_currMacroScope_2544_);
lean_ctor_set(v___x_2550_, 12, v_cancelTk_x3f_2546_);
lean_ctor_set(v___x_2550_, 13, v_inheritedTraceOptions_2548_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*14, v_diag_2545_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*14 + 1, v_suppressElabErrors_2547_);
v___x_2551_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2526_, v___y_2528_, v___y_2529_, v___x_2550_, v___y_2531_);
lean_dec_ref_known(v___x_2550_, 14);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2552_, lean_object* v_msg_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2552_, v_msg_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec(v_ref_2552_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2561_, lean_object* v_msg_2562_, lean_object* v_declHint_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v_a_2571_; lean_object* v___x_2572_; 
v___x_2570_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2562_, v_declHint_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref(v___x_2570_);
v___x_2572_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2561_, v_a_2571_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2573_, lean_object* v_msg_2574_, lean_object* v_declHint_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2573_, v_msg_2574_, v_declHint_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v_ref_2573_);
return v_res_2582_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2585_ = l_Lean_stringToMessageData(v___x_2584_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2588_ = l_Lean_stringToMessageData(v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2589_, lean_object* v_constName_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2597_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2598_ = 0;
lean_inc(v_constName_2590_);
v___x_2599_ = l_Lean_MessageData_ofConstName(v_constName_2590_, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2597_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2589_, v___x_2602_, v_constName_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2604_, lean_object* v_constName_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2604_, v_constName_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec(v_ref_2604_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_ref_2620_; lean_object* v___x_2621_; 
v_ref_2620_ = lean_ctor_get(v___y_2617_, 5);
v___x_2621_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2620_, v_constName_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; lean_object* v_env_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2637_ = lean_st_ref_get(v___y_2635_);
v_env_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc_ref(v_env_2638_);
lean_dec(v___x_2637_);
v___x_2639_ = 0;
lean_inc(v_constName_2630_);
v___x_2640_ = l_Lean_Environment_find_x3f(v_env_2638_, v_constName_2630_, v___x_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2641_;
}
else
{
lean_object* v_val_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v_constName_2630_);
v_val_2642_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2640_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_val_2642_);
lean_dec(v___x_2640_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set_tag(v___x_2644_, 0);
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_val_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
return v_res_2657_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2662_ = lean_unsigned_to_nat(53u);
v___x_2663_ = lean_unsigned_to_nat(62u);
v___x_2664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2666_ = l_mkPanicMessageWithDecl(v___x_2665_, v___x_2664_, v___x_2663_, v___x_2662_, v___x_2661_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2667_, size_t v_i_2668_, lean_object* v_bs_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = lean_usize_dec_lt(v_i_2668_, v_sz_2667_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_bs_2669_);
return v___x_2677_;
}
else
{
lean_object* v_v_2678_; lean_object* v___x_2679_; 
v_v_2678_ = lean_array_uget_borrowed(v_bs_2669_, v_i_2668_);
lean_inc(v_v_2678_);
v___x_2679_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2678_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; lean_object* v_bs_x27_2682_; lean_object* v_a_2684_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = lean_unsigned_to_nat(0u);
v_bs_x27_2682_ = lean_array_uset(v_bs_2669_, v_i_2668_, v___x_2681_);
if (lean_obj_tag(v_a_2680_) == 6)
{
lean_object* v_val_2689_; lean_object* v_numFields_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; 
v_val_2689_ = lean_ctor_get(v_a_2680_, 0);
lean_inc_ref(v_val_2689_);
lean_dec_ref_known(v_a_2680_, 1);
v_numFields_2690_ = lean_ctor_get(v_val_2689_, 4);
lean_inc(v_numFields_2690_);
lean_dec_ref(v_val_2689_);
v___x_2691_ = 0;
v___x_2692_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2692_, 0, v_numFields_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2681_);
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*2, v___x_2691_);
v_a_2684_ = v___x_2692_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_dec(v_a_2680_);
v___x_2693_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2694_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2693_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v_a_2684_ = v_a_2695_;
goto v___jp_2683_;
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v_bs_x27_2682_);
v_a_2696_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2694_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2694_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
v___jp_2683_:
{
size_t v___x_2685_; size_t v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = ((size_t)1ULL);
v___x_2686_ = lean_usize_add(v_i_2668_, v___x_2685_);
v___x_2687_ = lean_array_uset(v_bs_x27_2682_, v_i_2668_, v_a_2684_);
v_i_2668_ = v___x_2686_;
v_bs_2669_ = v___x_2687_;
goto _start;
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_bs_2669_);
v_a_2704_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2679_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2679_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2712_, lean_object* v_i_2713_, lean_object* v_bs_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
size_t v_sz_boxed_2721_; size_t v_i_boxed_2722_; lean_object* v_res_2723_; 
v_sz_boxed_2721_ = lean_unbox_usize(v_sz_2712_);
lean_dec(v_sz_2712_);
v_i_boxed_2722_ = lean_unbox_usize(v_i_2713_);
lean_dec(v_i_2713_);
v_res_2723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2721_, v_i_boxed_2722_, v_bs_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
return v_res_2723_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_unsigned_to_nat(16u);
v___x_2726_ = lean_mk_array(v___x_2725_, v___x_2724_);
return v___x_2726_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2728_ = lean_unsigned_to_nat(0u);
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v___x_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2732_, uint8_t v_alsoCasesOn_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = l_Lean_Expr_isApp(v_e_2732_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v_e_2732_);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Expr_getAppFn(v_e_2732_);
if (lean_obj_tag(v___x_2746_) == 4)
{
lean_object* v_declName_2747_; lean_object* v_us_2748_; lean_object* v___x_2749_; lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2904_; 
v_declName_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc_n(v_declName_2747_, 2);
v_us_2748_ = lean_ctor_get(v___x_2746_, 1);
lean_inc(v_us_2748_);
lean_dec_ref_known(v___x_2746_, 2);
v___x_2749_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2747_, v___y_2738_);
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2904_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2904_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
if (lean_obj_tag(v_a_2750_) == 1)
{
lean_object* v_val_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2796_; 
v_val_2754_ = lean_ctor_get(v_a_2750_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_a_2750_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2756_ = v_a_2750_;
v_isShared_2757_ = v_isSharedCheck_2796_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_val_2754_);
lean_dec(v_a_2750_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2796_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v_dummy_2758_; lean_object* v_nargs_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v_args_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v_dummy_2758_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2759_ = l_Lean_Expr_getAppNumArgs(v_e_2732_);
lean_inc(v_nargs_2759_);
v___x_2760_ = lean_mk_array(v_nargs_2759_, v_dummy_2758_);
v___x_2761_ = lean_unsigned_to_nat(1u);
v___x_2762_ = lean_nat_sub(v_nargs_2759_, v___x_2761_);
lean_dec(v_nargs_2759_);
v_args_2763_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2732_, v___x_2760_, v___x_2762_);
v___x_2764_ = lean_array_get_size(v_args_2763_);
v___x_2765_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2754_);
v___x_2766_ = lean_nat_dec_lt(v___x_2764_, v___x_2765_);
lean_dec(v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v_numParams_2767_; lean_object* v_numDiscrs_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v_numParams_2767_ = lean_ctor_get(v_val_2754_, 0);
v_numDiscrs_2768_ = lean_ctor_get(v_val_2754_, 1);
v___x_2769_ = lean_array_mk(v_us_2748_);
v___x_2770_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2767_);
v___x_2771_ = l_Array_extract___redArg(v_args_2763_, v___x_2770_, v_numParams_2767_);
v___x_2772_ = l_Lean_instInhabitedExpr;
v___x_2773_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2754_);
v___x_2774_ = lean_array_get(v___x_2772_, v_args_2763_, v___x_2773_);
lean_dec(v___x_2773_);
v___x_2775_ = lean_nat_add(v_numParams_2767_, v___x_2761_);
v___x_2776_ = lean_nat_add(v___x_2775_, v_numDiscrs_2768_);
lean_inc(v___x_2776_);
lean_inc_ref_n(v_args_2763_, 2);
v___x_2777_ = l_Array_toSubarray___redArg(v_args_2763_, v___x_2775_, v___x_2776_);
v___x_2778_ = l_Subarray_copy___redArg(v___x_2777_);
v___x_2779_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2754_);
v___x_2780_ = lean_nat_add(v___x_2776_, v___x_2779_);
lean_dec(v___x_2779_);
lean_inc(v___x_2780_);
v___x_2781_ = l_Array_toSubarray___redArg(v_args_2763_, v___x_2776_, v___x_2780_);
v___x_2782_ = l_Subarray_copy___redArg(v___x_2781_);
v___x_2783_ = l_Array_toSubarray___redArg(v_args_2763_, v___x_2780_, v___x_2764_);
v___x_2784_ = l_Subarray_copy___redArg(v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2785_, 0, v_val_2754_);
lean_ctor_set(v___x_2785_, 1, v_declName_2747_);
lean_ctor_set(v___x_2785_, 2, v___x_2769_);
lean_ctor_set(v___x_2785_, 3, v___x_2771_);
lean_ctor_set(v___x_2785_, 4, v___x_2774_);
lean_ctor_set(v___x_2785_, 5, v___x_2778_);
lean_ctor_set(v___x_2785_, 6, v___x_2782_);
lean_ctor_set(v___x_2785_, 7, v___x_2784_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2785_);
v___x_2787_ = v___x_2756_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2787_);
v___x_2789_ = v___x_2752_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2794_; 
lean_dec_ref(v_args_2763_);
lean_del_object(v___x_2756_);
lean_dec(v_val_2754_);
lean_dec(v_us_2748_);
lean_dec(v_declName_2747_);
v___x_2792_ = lean_box(0);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2792_);
v___x_2794_ = v___x_2752_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
else
{
lean_object* v___x_2797_; 
lean_del_object(v___x_2752_);
lean_dec(v_a_2750_);
v___x_2797_ = lean_st_ref_get(v___y_2738_);
if (v_alsoCasesOn_2733_ == 0)
{
lean_dec(v___x_2797_);
lean_dec(v_us_2748_);
lean_dec(v_declName_2747_);
lean_dec_ref(v_e_2732_);
goto v___jp_2740_;
}
else
{
lean_object* v_env_2798_; uint8_t v___x_2799_; 
v_env_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc_ref(v_env_2798_);
lean_dec(v___x_2797_);
lean_inc(v_declName_2747_);
v___x_2799_ = l_Lean_isCasesOnRecursor(v_env_2798_, v_declName_2747_);
if (v___x_2799_ == 0)
{
lean_dec(v_us_2748_);
lean_dec(v_declName_2747_);
lean_dec_ref(v_e_2732_);
goto v___jp_2740_;
}
else
{
lean_object* v_indName_2800_; lean_object* v___x_2801_; 
v_indName_2800_ = l_Lean_Name_getPrefix(v_declName_2747_);
v___x_2801_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2800_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2895_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2895_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2895_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
if (lean_obj_tag(v_a_2802_) == 5)
{
lean_object* v_val_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2890_; 
v_val_2806_ = lean_ctor_get(v_a_2802_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_a_2802_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2808_ = v_a_2802_;
v_isShared_2809_ = v_isSharedCheck_2890_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_val_2806_);
lean_dec(v_a_2802_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2890_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v_toConstantVal_2810_; lean_object* v_numParams_2811_; lean_object* v_numIndices_2812_; lean_object* v_ctors_2813_; lean_object* v_nargs_2814_; lean_object* v_dummy_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v_args_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v_toConstantVal_2810_ = lean_ctor_get(v_val_2806_, 0);
lean_inc_ref(v_toConstantVal_2810_);
v_numParams_2811_ = lean_ctor_get(v_val_2806_, 1);
lean_inc(v_numParams_2811_);
v_numIndices_2812_ = lean_ctor_get(v_val_2806_, 2);
lean_inc(v_numIndices_2812_);
v_ctors_2813_ = lean_ctor_get(v_val_2806_, 4);
lean_inc(v_ctors_2813_);
v_nargs_2814_ = l_Lean_Expr_getAppNumArgs(v_e_2732_);
v_dummy_2815_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2814_);
v___x_2816_ = lean_mk_array(v_nargs_2814_, v_dummy_2815_);
v___x_2817_ = lean_unsigned_to_nat(1u);
v___x_2818_ = lean_nat_sub(v_nargs_2814_, v___x_2817_);
lean_dec(v_nargs_2814_);
v_args_2819_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2732_, v___x_2816_, v___x_2818_);
v___x_2820_ = lean_nat_add(v_numParams_2811_, v___x_2817_);
v___x_2821_ = lean_nat_add(v___x_2820_, v_numIndices_2812_);
v___x_2822_ = lean_nat_add(v___x_2821_, v___x_2817_);
lean_dec(v___x_2821_);
v___x_2823_ = l_Lean_InductiveVal_numCtors(v_val_2806_);
lean_dec_ref(v_val_2806_);
v___x_2824_ = lean_nat_add(v___x_2822_, v___x_2823_);
lean_dec(v___x_2823_);
v___x_2825_ = lean_array_get_size(v_args_2819_);
v___x_2826_ = lean_nat_dec_le(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2829_; 
lean_dec(v___x_2824_);
lean_dec(v___x_2822_);
lean_dec(v___x_2820_);
lean_dec_ref(v_args_2819_);
lean_dec(v_ctors_2813_);
lean_dec(v_numIndices_2812_);
lean_dec(v_numParams_2811_);
lean_dec_ref(v_toConstantVal_2810_);
lean_del_object(v___x_2808_);
lean_dec(v_us_2748_);
lean_dec(v_declName_2747_);
v___x_2827_ = lean_box(0);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2827_);
v___x_2829_ = v___x_2804_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
else
{
lean_object* v___x_2831_; lean_object* v_params_2832_; lean_object* v___x_2833_; lean_object* v_motive_2834_; lean_object* v_discrs_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v_discrInfos_2838_; lean_object* v_alts_2839_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_lower_2881_; lean_object* v_upper_2882_; uint8_t v___x_2889_; 
lean_del_object(v___x_2804_);
v___x_2831_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2811_);
lean_inc_ref_n(v_args_2819_, 3);
v_params_2832_ = l_Array_toSubarray___redArg(v_args_2819_, v___x_2831_, v_numParams_2811_);
v___x_2833_ = l_Lean_instInhabitedExpr;
v_motive_2834_ = lean_array_get(v___x_2833_, v_args_2819_, v_numParams_2811_);
lean_dec(v_numParams_2811_);
lean_inc(v___x_2822_);
v_discrs_2835_ = l_Array_toSubarray___redArg(v_args_2819_, v___x_2820_, v___x_2822_);
v___x_2836_ = lean_nat_add(v_numIndices_2812_, v___x_2817_);
lean_dec(v_numIndices_2812_);
v___x_2837_ = lean_box(0);
v_discrInfos_2838_ = lean_mk_array(v___x_2836_, v___x_2837_);
lean_inc(v___x_2824_);
v_alts_2839_ = l_Array_toSubarray___redArg(v_args_2819_, v___x_2822_, v___x_2824_);
v___x_2889_ = lean_nat_dec_le(v___x_2824_, v___x_2831_);
if (v___x_2889_ == 0)
{
v_lower_2881_ = v___x_2824_;
v_upper_2882_ = v___x_2825_;
goto v___jp_2880_;
}
else
{
lean_dec(v___x_2824_);
v_lower_2881_ = v___x_2831_;
v_upper_2882_ = v___x_2825_;
goto v___jp_2880_;
}
v___jp_2840_:
{
lean_object* v___x_2843_; size_t v_sz_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v___x_2843_ = lean_array_mk(v_ctors_2813_);
v_sz_2844_ = lean_array_size(v___x_2843_);
v___x_2845_ = ((size_t)0ULL);
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2844_, v___x_2845_, v___x_2843_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2871_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2871_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2871_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_start_2851_; lean_object* v_stop_2852_; lean_object* v_start_2853_; lean_object* v_stop_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v_start_2851_ = lean_ctor_get(v_params_2832_, 1);
lean_inc(v_start_2851_);
v_stop_2852_ = lean_ctor_get(v_params_2832_, 2);
lean_inc(v_stop_2852_);
v_start_2853_ = lean_ctor_get(v_discrs_2835_, 1);
lean_inc(v_start_2853_);
v_stop_2854_ = lean_ctor_get(v_discrs_2835_, 2);
lean_inc(v_stop_2854_);
v___x_2855_ = lean_nat_sub(v_stop_2852_, v_start_2851_);
lean_dec(v_start_2851_);
lean_dec(v_stop_2852_);
v___x_2856_ = lean_nat_sub(v_stop_2854_, v_start_2853_);
lean_dec(v_start_2853_);
lean_dec(v_stop_2854_);
v___x_2857_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2858_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2855_);
lean_ctor_set(v___x_2858_, 1, v___x_2856_);
lean_ctor_set(v___x_2858_, 2, v_a_2847_);
lean_ctor_set(v___x_2858_, 3, v___y_2842_);
lean_ctor_set(v___x_2858_, 4, v_discrInfos_2838_);
lean_ctor_set(v___x_2858_, 5, v___x_2857_);
v___x_2859_ = lean_array_mk(v_us_2748_);
v___x_2860_ = l_Subarray_copy___redArg(v_params_2832_);
v___x_2861_ = l_Subarray_copy___redArg(v_discrs_2835_);
v___x_2862_ = l_Subarray_copy___redArg(v_alts_2839_);
v___x_2863_ = l_Subarray_copy___redArg(v___y_2841_);
v___x_2864_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2858_);
lean_ctor_set(v___x_2864_, 1, v_declName_2747_);
lean_ctor_set(v___x_2864_, 2, v___x_2859_);
lean_ctor_set(v___x_2864_, 3, v___x_2860_);
lean_ctor_set(v___x_2864_, 4, v_motive_2834_);
lean_ctor_set(v___x_2864_, 5, v___x_2861_);
lean_ctor_set(v___x_2864_, 6, v___x_2862_);
lean_ctor_set(v___x_2864_, 7, v___x_2863_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 1);
lean_ctor_set(v___x_2808_, 0, v___x_2864_);
v___x_2866_ = v___x_2808_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2868_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2866_);
v___x_2868_ = v___x_2849_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec_ref(v_alts_2839_);
lean_dec_ref(v_discrInfos_2838_);
lean_dec_ref(v_discrs_2835_);
lean_dec(v_motive_2834_);
lean_dec_ref(v_params_2832_);
lean_del_object(v___x_2808_);
lean_dec(v_us_2748_);
lean_dec(v_declName_2747_);
v_a_2872_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2846_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2846_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
v___jp_2880_:
{
lean_object* v_levelParams_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v_levelParams_2883_ = lean_ctor_get(v_toConstantVal_2810_, 1);
lean_inc(v_levelParams_2883_);
lean_dec_ref(v_toConstantVal_2810_);
v___x_2884_ = l_Array_toSubarray___redArg(v_args_2819_, v_lower_2881_, v_upper_2882_);
v___x_2885_ = l_List_lengthTR___redArg(v_levelParams_2883_);
lean_dec(v_levelParams_2883_);
v___x_2886_ = l_List_lengthTR___redArg(v_us_2748_);
v___x_2887_ = lean_nat_dec_eq(v___x_2885_, v___x_2886_);
lean_dec(v___x_2886_);
lean_dec(v___x_2885_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
v___x_2888_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2841_ = v___x_2884_;
v___y_2842_ = v___x_2888_;
goto v___jp_2840_;
}
else
{
v___y_2841_ = v___x_2884_;
v___y_2842_ = v___x_2837_;
goto v___jp_2840_;
}
}
}
}
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
lean_dec(v_a_2802_);
lean_dec(v_us_2748_);
lean_dec(v_declName_2747_);
lean_dec_ref(v_e_2732_);
v___x_2891_ = lean_box(0);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2891_);
v___x_2893_ = v___x_2804_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_us_2748_);
lean_dec(v_declName_2747_);
lean_dec_ref(v_e_2732_);
v_a_2896_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2801_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2801_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
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
lean_dec_ref(v___x_2746_);
lean_dec_ref(v_e_2732_);
goto v___jp_2740_;
}
}
v___jp_2740_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_box(0);
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2905_, lean_object* v_alsoCasesOn_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2913_; lean_object* v_res_2914_; 
v_alsoCasesOn_boxed_2913_ = lean_unbox(v_alsoCasesOn_2906_);
v_res_2914_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2905_, v_alsoCasesOn_boxed_2913_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
if (lean_obj_tag(v_a_2915_) == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = l_List_reverse___redArg(v_a_2916_);
return v___x_2917_;
}
else
{
lean_object* v_head_2918_; lean_object* v_tail_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2928_; 
v_head_2918_ = lean_ctor_get(v_a_2915_, 0);
v_tail_2919_ = lean_ctor_get(v_a_2915_, 1);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_a_2915_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2921_ = v_a_2915_;
v_isShared_2922_ = v_isSharedCheck_2928_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_tail_2919_);
lean_inc(v_head_2918_);
lean_dec(v_a_2915_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2928_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2923_ = l_Lean_MessageData_ofExpr(v_head_2918_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v_a_2916_);
lean_ctor_set(v___x_2921_, 0, v___x_2923_);
v___x_2925_ = v___x_2921_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_a_2916_);
v___x_2925_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
v_a_2915_ = v_tail_2919_;
v_a_2916_ = v___x_2925_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
lean_object* v_fnName_2931_; uint8_t v___x_2932_; 
v_fnName_2931_ = lean_ctor_get(v_x_2930_, 0);
v___x_2932_ = l_Lean_Expr_isConstOf(v_x_2929_, v_fnName_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2933_, lean_object* v_x_2934_){
_start:
{
uint8_t v_res_2935_; lean_object* v_r_2936_; 
v_res_2935_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2933_, v_x_2934_);
lean_dec_ref(v_x_2934_);
lean_dec_ref(v_x_2933_);
v_r_2936_ = lean_box(v_res_2935_);
return v_r_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2937_, lean_object* v_type_2938_, lean_object* v_val_2939_, lean_object* v_k_2940_, uint8_t v_nondep_2941_, uint8_t v_kind_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___f_2949_; lean_object* v___x_2950_; 
lean_inc(v___y_2943_);
v___f_2949_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2949_, 0, v_k_2940_);
lean_closure_set(v___f_2949_, 1, v___y_2943_);
v___x_2950_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2937_, v_type_2938_, v_val_2939_, v___f_2949_, v_nondep_2941_, v_kind_2942_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2950_) == 0)
{
return v___x_2950_;
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2959_, lean_object* v_type_2960_, lean_object* v_val_2961_, lean_object* v_k_2962_, lean_object* v_nondep_2963_, lean_object* v_kind_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
uint8_t v_nondep_boxed_2971_; uint8_t v_kind_boxed_2972_; lean_object* v_res_2973_; 
v_nondep_boxed_2971_ = lean_unbox(v_nondep_2963_);
v_kind_boxed_2972_ = lean_unbox(v_kind_2964_);
v_res_2973_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2959_, v_type_2960_, v_val_2961_, v_k_2962_, v_nondep_boxed_2971_, v_kind_boxed_2972_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2974_, uint8_t v_usedLetOnly_2975_, lean_object* v_x_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; 
lean_inc(v___y_2981_);
lean_inc_ref(v___y_2980_);
lean_inc(v___y_2979_);
lean_inc_ref(v___y_2978_);
lean_inc(v___y_2977_);
lean_inc_ref(v_x_2976_);
v___x_2983_ = lean_apply_7(v_k_2974_, v_x_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, lean_box(0));
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = lean_unsigned_to_nat(1u);
v___x_2986_ = lean_mk_empty_array_with_capacity(v___x_2985_);
v___x_2987_ = lean_array_push(v___x_2986_, v_x_2976_);
v___x_2988_ = 0;
v___x_2989_ = 1;
v___x_2990_ = l_Lean_Meta_mkLetFVars(v___x_2987_, v_a_2984_, v_usedLetOnly_2975_, v___x_2988_, v___x_2989_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec_ref(v___x_2987_);
return v___x_2990_;
}
else
{
lean_dec_ref(v_x_2976_);
return v___x_2983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2991_, lean_object* v_usedLetOnly_2992_, lean_object* v_x_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
uint8_t v_usedLetOnly_boxed_3000_; lean_object* v_res_3001_; 
v_usedLetOnly_boxed_3000_ = lean_unbox(v_usedLetOnly_2992_);
v_res_3001_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2991_, v_usedLetOnly_boxed_3000_, v_x_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_3002_, lean_object* v_type_3003_, lean_object* v_val_3004_, lean_object* v_k_3005_, uint8_t v_nondep_3006_, uint8_t v_kind_3007_, uint8_t v_usedLetOnly_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v___x_3015_; lean_object* v___f_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_box(v_usedLetOnly_3008_);
v___f_3016_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3016_, 0, v_k_3005_);
lean_closure_set(v___f_3016_, 1, v___x_3015_);
v___x_3017_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3002_, v_type_3003_, v_val_3004_, v___f_3016_, v_nondep_3006_, v_kind_3007_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_3018_, lean_object* v_type_3019_, lean_object* v_val_3020_, lean_object* v_k_3021_, lean_object* v_nondep_3022_, lean_object* v_kind_3023_, lean_object* v_usedLetOnly_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
uint8_t v_nondep_boxed_3031_; uint8_t v_kind_boxed_3032_; uint8_t v_usedLetOnly_boxed_3033_; lean_object* v_res_3034_; 
v_nondep_boxed_3031_ = lean_unbox(v_nondep_3022_);
v_kind_boxed_3032_ = lean_unbox(v_kind_3023_);
v_usedLetOnly_boxed_3033_ = lean_unbox(v_usedLetOnly_3024_);
v_res_3034_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_3018_, v_type_3019_, v_val_3020_, v_k_3021_, v_nondep_boxed_3031_, v_kind_boxed_3032_, v_usedLetOnly_boxed_3033_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_3035_, lean_object* v_positions_3036_, lean_object* v_recFnNames_3037_, lean_object* v_containsRecFn_3038_, lean_object* v_below_3039_, size_t v_sz_3040_, size_t v_i_3041_, lean_object* v_bs_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_usize_dec_lt(v_i_3041_, v_sz_3040_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; 
lean_dec_ref(v_below_3039_);
lean_dec_ref(v_containsRecFn_3038_);
lean_dec_ref(v_recFnNames_3037_);
lean_dec_ref(v_positions_3036_);
lean_dec_ref(v_recArgInfos_3035_);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_bs_3042_);
return v___x_3050_;
}
else
{
lean_object* v_v_3051_; lean_object* v___x_3052_; 
v_v_3051_ = lean_array_uget_borrowed(v_bs_3042_, v_i_3041_);
lean_inc_ref(v___y_3046_);
lean_inc(v_v_3051_);
lean_inc_ref(v_below_3039_);
lean_inc_ref(v_containsRecFn_3038_);
lean_inc_ref(v_recFnNames_3037_);
lean_inc_ref(v_positions_3036_);
lean_inc_ref(v_recArgInfos_3035_);
v___x_3052_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3035_, v_positions_3036_, v_recFnNames_3037_, v_containsRecFn_3038_, v_below_3039_, v_v_3051_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v_bs_x27_3055_; size_t v___x_3056_; size_t v___x_3057_; lean_object* v___x_3058_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = lean_unsigned_to_nat(0u);
v_bs_x27_3055_ = lean_array_uset(v_bs_3042_, v_i_3041_, v___x_3054_);
v___x_3056_ = ((size_t)1ULL);
v___x_3057_ = lean_usize_add(v_i_3041_, v___x_3056_);
v___x_3058_ = lean_array_uset(v_bs_x27_3055_, v_i_3041_, v_a_3053_);
v_i_3041_ = v___x_3057_;
v_bs_3042_ = v___x_3058_;
goto _start;
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v_bs_3042_);
lean_dec_ref(v_below_3039_);
lean_dec_ref(v_containsRecFn_3038_);
lean_dec_ref(v_recFnNames_3037_);
lean_dec_ref(v_positions_3036_);
lean_dec_ref(v_recArgInfos_3035_);
v_a_3060_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3052_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3052_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3070_ = l_Lean_stringToMessageData(v___x_3069_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3073_ = l_Lean_stringToMessageData(v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3074_, lean_object* v_positions_3075_, lean_object* v_recFnNames_3076_, lean_object* v_containsRecFn_3077_, lean_object* v_below_3078_, lean_object* v_e_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v_x_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
if (lean_obj_tag(v_x_3080_) == 5)
{
lean_object* v_fn_3089_; lean_object* v_arg_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_fn_3089_ = lean_ctor_get(v_x_3080_, 0);
lean_inc_ref(v_fn_3089_);
v_arg_3090_ = lean_ctor_get(v_x_3080_, 1);
lean_inc_ref(v_arg_3090_);
lean_dec_ref_known(v_x_3080_, 2);
v___x_3091_ = lean_array_set(v_x_3081_, v_x_3082_, v_arg_3090_);
v___x_3092_ = lean_unsigned_to_nat(1u);
v___x_3093_ = lean_nat_sub(v_x_3082_, v___x_3092_);
lean_dec(v_x_3082_);
v_x_3080_ = v_fn_3089_;
v_x_3081_ = v___x_3091_;
v_x_3082_ = v___x_3093_;
goto _start;
}
else
{
lean_object* v___f_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
lean_dec(v_x_3082_);
lean_inc_ref(v_x_3080_);
v___f_3095_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3095_, 0, v_x_3080_);
v___x_3096_ = lean_unsigned_to_nat(0u);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3095_, v_recArgInfos_3074_, v___x_3096_);
if (lean_obj_tag(v___x_3097_) == 1)
{
lean_object* v_val_3098_; lean_object* v___x_3099_; lean_object* v___y_3101_; lean_object* v_recArgPos_3127_; lean_object* v_indGroupInst_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
lean_dec_ref(v_x_3080_);
v_val_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_val_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v___x_3099_ = lean_array_fget_borrowed(v_recArgInfos_3074_, v_val_3098_);
v_recArgPos_3127_ = lean_ctor_get(v___x_3099_, 2);
v_indGroupInst_3128_ = lean_ctor_get(v___x_3099_, 4);
v___x_3129_ = lean_array_get_size(v_x_3081_);
v___x_3130_ = lean_nat_dec_lt(v_recArgPos_3127_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec(v_val_3098_);
lean_dec_ref(v_x_3081_);
lean_dec_ref(v_below_3078_);
lean_dec_ref(v_containsRecFn_3077_);
lean_dec_ref(v_recFnNames_3076_);
lean_dec_ref(v_positions_3075_);
lean_dec_ref(v_recArgInfos_3074_);
v___x_3131_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3132_ = l_Lean_indentExpr(v_e_3079_);
v___x_3133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3131_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3133_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_array_fget_borrowed(v_x_3081_, v_recArgPos_3127_);
lean_inc_ref(v___y_3086_);
lean_inc(v___x_3135_);
lean_inc_ref(v_below_3078_);
lean_inc_ref(v_containsRecFn_3077_);
lean_inc_ref(v_recFnNames_3076_);
lean_inc_ref(v_positions_3075_);
lean_inc_ref(v_recArgInfos_3074_);
v___x_3136_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3074_, v_positions_3075_, v_recFnNames_3076_, v_containsRecFn_3077_, v_below_3078_, v___x_3135_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v_params_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3136_, 1);
v_params_3138_ = lean_ctor_get(v_indGroupInst_3128_, 2);
v___x_3139_ = lean_array_get_size(v_params_3138_);
lean_inc_ref(v_positions_3075_);
lean_inc_ref(v_below_3078_);
v___x_3140_ = l_Lean_Elab_Structural_toBelow(v_below_3078_, v___x_3139_, v_positions_3075_, v_val_3098_, v_a_3137_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_dec_ref(v_e_3079_);
v___y_3101_ = v___x_3140_;
goto v___jp_3100_;
}
else
{
lean_object* v_a_3141_; uint8_t v___y_3143_; uint8_t v___x_3148_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
v___x_3148_ = l_Lean_Exception_isInterrupt(v_a_3141_);
if (v___x_3148_ == 0)
{
uint8_t v___x_3149_; 
v___x_3149_ = l_Lean_Exception_isRuntime(v_a_3141_);
v___y_3143_ = v___x_3149_;
goto v___jp_3142_;
}
else
{
lean_dec(v_a_3141_);
v___y_3143_ = v___x_3148_;
goto v___jp_3142_;
}
v___jp_3142_:
{
if (v___y_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_dec_ref_known(v___x_3140_, 1);
v___x_3144_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3145_ = l_Lean_indentExpr(v_e_3079_);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3146_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
v___y_3101_ = v___x_3147_;
goto v___jp_3100_;
}
else
{
lean_dec_ref(v_e_3079_);
v___y_3101_ = v___x_3140_;
goto v___jp_3100_;
}
}
}
}
else
{
lean_dec(v_val_3098_);
lean_dec_ref(v_x_3081_);
lean_dec_ref(v_e_3079_);
lean_dec_ref(v_below_3078_);
lean_dec_ref(v_containsRecFn_3077_);
lean_dec_ref(v_recFnNames_3076_);
lean_dec_ref(v_positions_3075_);
lean_dec_ref(v_recArgInfos_3074_);
return v___x_3136_;
}
}
v___jp_3100_:
{
if (lean_obj_tag(v___y_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v_fixedParamPerm_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_snd_3106_; size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v_a_3102_ = lean_ctor_get(v___y_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___y_3101_, 1);
v_fixedParamPerm_3103_ = lean_ctor_get(v___x_3099_, 1);
v___x_3104_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3103_, v_x_3081_);
lean_dec_ref(v_x_3081_);
lean_inc(v___x_3099_);
v___x_3105_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3099_, v___x_3104_);
v_snd_3106_ = lean_ctor_get(v___x_3105_, 1);
lean_inc(v_snd_3106_);
lean_dec_ref(v___x_3105_);
v_sz_3107_ = lean_array_size(v_snd_3106_);
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3074_, v_positions_3075_, v_recFnNames_3076_, v_containsRecFn_3077_, v_below_3078_, v_sz_3107_, v___x_3108_, v_snd_3106_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3118_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3114_ = l_Lean_mkAppN(v_a_3102_, v_a_3110_);
lean_dec(v_a_3110_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3114_);
v___x_3116_ = v___x_3112_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_a_3102_);
v_a_3119_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3109_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3109_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_dec_ref(v_x_3081_);
lean_dec_ref(v_below_3078_);
lean_dec_ref(v_containsRecFn_3077_);
lean_dec_ref(v_recFnNames_3076_);
lean_dec_ref(v_positions_3075_);
lean_dec_ref(v_recArgInfos_3074_);
return v___y_3101_;
}
}
}
else
{
lean_object* v___x_3150_; 
lean_dec(v___x_3097_);
lean_dec_ref(v_e_3079_);
lean_inc_ref(v___y_3086_);
lean_inc_ref(v_below_3078_);
lean_inc_ref(v_containsRecFn_3077_);
lean_inc_ref(v_recFnNames_3076_);
lean_inc_ref(v_positions_3075_);
lean_inc_ref(v_recArgInfos_3074_);
v___x_3150_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3074_, v_positions_3075_, v_recFnNames_3076_, v_containsRecFn_3077_, v_below_3078_, v_x_3080_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; size_t v_sz_3152_; size_t v___x_3153_; lean_object* v___x_3154_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v_sz_3152_ = lean_array_size(v_x_3081_);
v___x_3153_ = ((size_t)0ULL);
v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3074_, v_positions_3075_, v_recFnNames_3076_, v_containsRecFn_3077_, v_below_3078_, v_sz_3152_, v___x_3153_, v_x_3081_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3163_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3163_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3163_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3159_ = l_Lean_mkAppN(v_a_3151_, v_a_3155_);
lean_dec(v_a_3155_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3159_);
v___x_3161_ = v___x_3157_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_a_3151_);
v_a_3164_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3154_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3154_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_dec_ref(v_x_3081_);
lean_dec_ref(v_below_3078_);
lean_dec_ref(v_containsRecFn_3077_);
lean_dec_ref(v_recFnNames_3076_);
lean_dec_ref(v_positions_3075_);
lean_dec_ref(v_recArgInfos_3074_);
return v___x_3150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3172_, lean_object* v_recArgInfos_3173_, lean_object* v_positions_3174_, lean_object* v_recFnNames_3175_, lean_object* v_containsRecFn_3176_, lean_object* v_below_3177_, uint8_t v___x_3178_, uint8_t v_a_3179_, lean_object* v_x_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_expr_instantiate1(v_body_3172_, v_x_3180_);
lean_inc_ref(v___y_3184_);
v___x_3188_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3173_, v_positions_3174_, v_recFnNames_3175_, v_containsRecFn_3176_, v_below_3177_, v___x_3187_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; lean_object* v___x_3194_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = lean_unsigned_to_nat(1u);
v___x_3191_ = lean_mk_empty_array_with_capacity(v___x_3190_);
v___x_3192_ = lean_array_push(v___x_3191_, v_x_3180_);
v___x_3193_ = 1;
v___x_3194_ = l_Lean_Meta_mkLambdaFVars(v___x_3192_, v_a_3189_, v___x_3178_, v_a_3179_, v___x_3178_, v_a_3179_, v___x_3193_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec_ref(v___x_3192_);
return v___x_3194_;
}
else
{
lean_dec_ref(v_x_3180_);
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3195_, lean_object* v_recArgInfos_3196_, lean_object* v_positions_3197_, lean_object* v_recFnNames_3198_, lean_object* v_containsRecFn_3199_, lean_object* v_below_3200_, lean_object* v___x_3201_, lean_object* v_a_3202_, lean_object* v_x_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
uint8_t v___x_32812__boxed_3210_; uint8_t v_a_32813__boxed_3211_; lean_object* v_res_3212_; 
v___x_32812__boxed_3210_ = lean_unbox(v___x_3201_);
v_a_32813__boxed_3211_ = lean_unbox(v_a_3202_);
v_res_3212_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3195_, v_recArgInfos_3196_, v_positions_3197_, v_recFnNames_3198_, v_containsRecFn_3199_, v_below_3200_, v___x_32812__boxed_3210_, v_a_32813__boxed_3211_, v_x_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v_body_3195_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3213_, lean_object* v_recArgInfos_3214_, lean_object* v_positions_3215_, lean_object* v_recFnNames_3216_, lean_object* v_containsRecFn_3217_, lean_object* v_below_3218_, uint8_t v___x_3219_, uint8_t v_a_3220_, lean_object* v_x_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = lean_expr_instantiate1(v_body_3213_, v_x_3221_);
lean_inc_ref(v___y_3225_);
v___x_3229_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3214_, v_positions_3215_, v_recFnNames_3216_, v_containsRecFn_3217_, v_below_3218_, v___x_3228_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___x_3229_, 1);
v___x_3231_ = lean_unsigned_to_nat(1u);
v___x_3232_ = lean_mk_empty_array_with_capacity(v___x_3231_);
v___x_3233_ = lean_array_push(v___x_3232_, v_x_3221_);
v___x_3234_ = 1;
v___x_3235_ = l_Lean_Meta_mkForallFVars(v___x_3233_, v_a_3230_, v___x_3219_, v_a_3220_, v_a_3220_, v___x_3234_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec_ref(v___x_3233_);
return v___x_3235_;
}
else
{
lean_dec_ref(v_x_3221_);
return v___x_3229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3236_, lean_object* v_recArgInfos_3237_, lean_object* v_positions_3238_, lean_object* v_recFnNames_3239_, lean_object* v_containsRecFn_3240_, lean_object* v_below_3241_, lean_object* v___x_3242_, lean_object* v_a_3243_, lean_object* v_x_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v___x_32830__boxed_3251_; uint8_t v_a_32831__boxed_3252_; lean_object* v_res_3253_; 
v___x_32830__boxed_3251_ = lean_unbox(v___x_3242_);
v_a_32831__boxed_3252_ = lean_unbox(v_a_3243_);
v_res_3253_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3236_, v_recArgInfos_3237_, v_positions_3238_, v_recFnNames_3239_, v_containsRecFn_3240_, v_below_3241_, v___x_32830__boxed_3251_, v_a_32831__boxed_3252_, v_x_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v_body_3236_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3254_, lean_object* v_recArgInfos_3255_, lean_object* v_positions_3256_, lean_object* v_recFnNames_3257_, lean_object* v_containsRecFn_3258_, lean_object* v_below_3259_, lean_object* v_x_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3254_, v_recArgInfos_3255_, v_positions_3256_, v_recFnNames_3257_, v_containsRecFn_3258_, v_below_3259_, v_x_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v_x_3260_);
lean_dec_ref(v_body_3254_);
return v_res_3267_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3272_ = l_Lean_stringToMessageData(v___x_3271_);
return v___x_3272_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3275_ = l_Lean_stringToMessageData(v___x_3274_);
return v___x_3275_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3278_ = l_Lean_stringToMessageData(v___x_3277_);
return v___x_3278_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3281_ = l_Lean_stringToMessageData(v___x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v_b_3282_, lean_object* v_recArgInfos_3283_, lean_object* v_positions_3284_, lean_object* v_recFnNames_3285_, lean_object* v_containsRecFn_3286_, uint8_t v___x_3287_, uint8_t v_a_3288_, lean_object* v___x_3289_, lean_object* v_a_3290_, lean_object* v_e_3291_, lean_object* v___x_3292_, lean_object* v_xs_3293_, lean_object* v_altBody_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v_options_3337_; uint8_t v_hasTrace_3338_; 
v_options_3337_ = lean_ctor_get(v___y_3298_, 2);
v_hasTrace_3338_ = lean_ctor_get_uint8(v_options_3337_, sizeof(void*)*1);
if (v_hasTrace_3338_ == 0)
{
lean_dec(v___x_3292_);
v___y_3314_ = v___y_3295_;
v___y_3315_ = v___y_3296_;
v___y_3316_ = v___y_3297_;
v___y_3317_ = v___y_3298_;
v___y_3318_ = v___y_3299_;
goto v___jp_3313_;
}
else
{
lean_object* v_inheritedTraceOptions_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v_inheritedTraceOptions_3339_ = lean_ctor_get(v___y_3298_, 13);
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3292_);
v___x_3341_ = l_Lean_Name_append(v___x_3340_, v___x_3292_);
v___x_3342_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3339_, v_options_3337_, v___x_3341_);
lean_dec(v___x_3341_);
if (v___x_3342_ == 0)
{
lean_dec(v___x_3292_);
v___y_3314_ = v___y_3295_;
v___y_3315_ = v___y_3296_;
v___y_3316_ = v___y_3297_;
v___y_3317_ = v___y_3298_;
v___y_3318_ = v___y_3299_;
goto v___jp_3313_;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3343_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3282_);
v___x_3344_ = l_Nat_reprFast(v_b_3282_);
v___x_3345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
v___x_3346_ = l_Lean_MessageData_ofFormat(v___x_3345_);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3343_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
lean_inc_ref(v_xs_3293_);
v___x_3350_ = lean_array_to_list(v_xs_3293_);
v___x_3351_ = lean_box(0);
v___x_3352_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3350_, v___x_3351_);
v___x_3353_ = l_Lean_MessageData_ofList(v___x_3352_);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3349_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3292_, v___x_3354_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_dec_ref_known(v___x_3355_, 1);
v___y_3314_ = v___y_3295_;
v___y_3315_ = v___y_3296_;
v___y_3316_ = v___y_3297_;
v___y_3317_ = v___y_3298_;
v___y_3318_ = v___y_3299_;
goto v___jp_3313_;
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec_ref(v_altBody_3294_);
lean_dec_ref(v_xs_3293_);
lean_dec_ref(v_e_3291_);
lean_dec_ref(v_a_3290_);
lean_dec_ref(v_containsRecFn_3286_);
lean_dec_ref(v_recFnNames_3285_);
lean_dec_ref(v_positions_3284_);
lean_dec_ref(v_recArgInfos_3283_);
lean_dec(v_b_3282_);
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
v___jp_3301_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = l_Lean_instInhabitedExpr;
v___x_3308_ = lean_array_get_borrowed(v___x_3307_, v_xs_3293_, v_b_3282_);
lean_dec(v_b_3282_);
lean_inc_ref(v___y_3305_);
lean_inc(v___x_3308_);
v___x_3309_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3283_, v_positions_3284_, v_recFnNames_3285_, v_containsRecFn_3286_, v___x_3308_, v_altBody_3294_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; uint8_t v___x_3311_; lean_object* v___x_3312_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3309_, 1);
v___x_3311_ = 1;
v___x_3312_ = l_Lean_Meta_mkLambdaFVars(v_xs_3293_, v_a_3310_, v___x_3287_, v_a_3288_, v___x_3287_, v_a_3288_, v___x_3311_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec_ref(v_xs_3293_);
return v___x_3312_;
}
else
{
lean_dec_ref(v_xs_3293_);
return v___x_3309_;
}
}
v___jp_3313_:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = lean_array_get_size(v_xs_3293_);
v___x_3320_ = lean_nat_dec_eq(v___x_3319_, v___x_3289_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v_altBody_3294_);
lean_dec_ref(v_xs_3293_);
lean_dec_ref(v_containsRecFn_3286_);
lean_dec_ref(v_recFnNames_3285_);
lean_dec_ref(v_positions_3284_);
lean_dec_ref(v_recArgInfos_3283_);
lean_dec(v_b_3282_);
v___x_3321_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3322_ = l_Lean_indentExpr(v_a_3290_);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = l_Lean_indentExpr(v_e_3291_);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3327_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
else
{
lean_dec_ref(v_e_3291_);
lean_dec_ref(v_a_3290_);
v___y_3302_ = v___y_3314_;
v___y_3303_ = v___y_3315_;
v___y_3304_ = v___y_3316_;
v___y_3305_ = v___y_3317_;
v___y_3306_ = v___y_3318_;
goto v___jp_3301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v_b_3364_ = _args[0];
lean_object* v_recArgInfos_3365_ = _args[1];
lean_object* v_positions_3366_ = _args[2];
lean_object* v_recFnNames_3367_ = _args[3];
lean_object* v_containsRecFn_3368_ = _args[4];
lean_object* v___x_3369_ = _args[5];
lean_object* v_a_3370_ = _args[6];
lean_object* v___x_3371_ = _args[7];
lean_object* v_a_3372_ = _args[8];
lean_object* v_e_3373_ = _args[9];
lean_object* v___x_3374_ = _args[10];
lean_object* v_xs_3375_ = _args[11];
lean_object* v_altBody_3376_ = _args[12];
lean_object* v___y_3377_ = _args[13];
lean_object* v___y_3378_ = _args[14];
lean_object* v___y_3379_ = _args[15];
lean_object* v___y_3380_ = _args[16];
lean_object* v___y_3381_ = _args[17];
lean_object* v___y_3382_ = _args[18];
_start:
{
uint8_t v___x_32904__boxed_3383_; uint8_t v_a_32905__boxed_3384_; lean_object* v_res_3385_; 
v___x_32904__boxed_3383_ = lean_unbox(v___x_3369_);
v_a_32905__boxed_3384_ = lean_unbox(v_a_3370_);
v_res_3385_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v_b_3364_, v_recArgInfos_3365_, v_positions_3366_, v_recFnNames_3367_, v_containsRecFn_3368_, v___x_32904__boxed_3383_, v_a_32905__boxed_3384_, v___x_3371_, v_a_3372_, v_e_3373_, v___x_3374_, v_xs_3375_, v_altBody_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec(v___x_3371_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3386_, lean_object* v_positions_3387_, lean_object* v_recFnNames_3388_, lean_object* v_containsRecFn_3389_, uint8_t v_a_3390_, lean_object* v_e_3391_, lean_object* v_as_3392_, lean_object* v_bs_3393_, lean_object* v_i_3394_, lean_object* v_cs_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3402_ = lean_array_get_size(v_as_3392_);
v___x_3403_ = lean_nat_dec_lt(v_i_3394_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_dec(v_i_3394_);
lean_dec_ref(v_e_3391_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v_cs_3395_);
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = lean_array_get_size(v_bs_3393_);
v___x_3406_ = lean_nat_dec_lt(v_i_3394_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; 
lean_dec(v_i_3394_);
lean_dec_ref(v_e_3391_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v_cs_3395_);
return v___x_3407_;
}
else
{
uint8_t v___x_3408_; lean_object* v___x_3409_; lean_object* v_a_3410_; lean_object* v_b_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; 
v___x_3408_ = 0;
v___x_3409_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3410_ = lean_array_fget_borrowed(v_as_3392_, v_i_3394_);
v_b_3411_ = lean_array_fget_borrowed(v_bs_3393_, v_i_3394_);
v___x_3412_ = lean_unsigned_to_nat(1u);
v___x_3413_ = lean_nat_add(v_b_3411_, v___x_3412_);
v___x_3414_ = lean_box(v___x_3408_);
v___x_3415_ = lean_box(v_a_3390_);
lean_inc_ref(v_e_3391_);
lean_inc_n(v_a_3410_, 2);
lean_inc(v___x_3413_);
lean_inc_ref(v_containsRecFn_3389_);
lean_inc_ref(v_recFnNames_3388_);
lean_inc_ref(v_positions_3387_);
lean_inc_ref(v_recArgInfos_3386_);
lean_inc(v_b_3411_);
v___f_3416_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 19, 11);
lean_closure_set(v___f_3416_, 0, v_b_3411_);
lean_closure_set(v___f_3416_, 1, v_recArgInfos_3386_);
lean_closure_set(v___f_3416_, 2, v_positions_3387_);
lean_closure_set(v___f_3416_, 3, v_recFnNames_3388_);
lean_closure_set(v___f_3416_, 4, v_containsRecFn_3389_);
lean_closure_set(v___f_3416_, 5, v___x_3414_);
lean_closure_set(v___f_3416_, 6, v___x_3415_);
lean_closure_set(v___f_3416_, 7, v___x_3413_);
lean_closure_set(v___f_3416_, 8, v_a_3410_);
lean_closure_set(v___f_3416_, 9, v_e_3391_);
lean_closure_set(v___f_3416_, 10, v___x_3409_);
v___x_3417_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3410_, v___x_3413_, v___f_3416_, v___x_3408_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3417_, 1);
v___x_3419_ = lean_nat_add(v_i_3394_, v___x_3412_);
lean_dec(v_i_3394_);
v___x_3420_ = lean_array_push(v_cs_3395_, v_a_3418_);
v_i_3394_ = v___x_3419_;
v_cs_3395_ = v___x_3420_;
goto _start;
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec_ref(v_cs_3395_);
lean_dec(v_i_3394_);
lean_dec_ref(v_e_3391_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v_a_3422_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3417_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3417_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
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
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3432_ = l_Lean_stringToMessageData(v___x_3431_);
return v___x_3432_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
return v___x_3435_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3439_, lean_object* v_positions_3440_, lean_object* v_recFnNames_3441_, lean_object* v_containsRecFn_3442_, lean_object* v_below_3443_, lean_object* v_e_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v_e_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___x_3464_; 
lean_inc_ref(v_containsRecFn_3442_);
lean_inc(v_a_3449_);
lean_inc_ref(v_a_3448_);
lean_inc(v_a_3447_);
lean_inc_ref(v_a_3446_);
lean_inc(v_a_3445_);
lean_inc_ref(v_e_3444_);
v___x_3464_ = lean_apply_7(v_containsRecFn_3442_, v_e_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, lean_box(0));
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3687_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3687_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3687_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_unbox(v_a_3465_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3471_; 
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v_e_3444_);
v___x_3471_ = v___x_3467_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_e_3444_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
else
{
uint8_t v___x_3473_; 
lean_del_object(v___x_3467_);
v___x_3473_ = 0;
switch(lean_obj_tag(v_e_3444_))
{
case 6:
{
lean_object* v_binderName_3474_; lean_object* v_binderType_3475_; lean_object* v_body_3476_; uint8_t v_binderInfo_3477_; lean_object* v___x_3478_; 
v_binderName_3474_ = lean_ctor_get(v_e_3444_, 0);
lean_inc(v_binderName_3474_);
v_binderType_3475_ = lean_ctor_get(v_e_3444_, 1);
lean_inc_ref(v_binderType_3475_);
v_body_3476_ = lean_ctor_get(v_e_3444_, 2);
lean_inc_ref(v_body_3476_);
v_binderInfo_3477_ = lean_ctor_get_uint8(v_e_3444_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3444_, 3);
lean_inc_ref(v_a_3448_);
lean_inc_ref(v_below_3443_);
lean_inc_ref(v_containsRecFn_3442_);
lean_inc_ref(v_recFnNames_3441_);
lean_inc_ref(v_positions_3440_);
lean_inc_ref(v_recArgInfos_3439_);
v___x_3478_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3439_, v_positions_3440_, v_recFnNames_3441_, v_containsRecFn_3442_, v_below_3443_, v_binderType_3475_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3480_; lean_object* v___f_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = lean_box(v___x_3473_);
v___f_3481_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3481_, 0, v_body_3476_);
lean_closure_set(v___f_3481_, 1, v_recArgInfos_3439_);
lean_closure_set(v___f_3481_, 2, v_positions_3440_);
lean_closure_set(v___f_3481_, 3, v_recFnNames_3441_);
lean_closure_set(v___f_3481_, 4, v_containsRecFn_3442_);
lean_closure_set(v___f_3481_, 5, v_below_3443_);
lean_closure_set(v___f_3481_, 6, v___x_3480_);
lean_closure_set(v___f_3481_, 7, v_a_3465_);
v___x_3482_ = 0;
v___x_3483_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3474_, v_binderInfo_3477_, v_a_3479_, v___f_3481_, v___x_3482_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec_ref(v_a_3448_);
return v___x_3483_;
}
else
{
lean_dec_ref(v_body_3476_);
lean_dec(v_binderName_3474_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
return v___x_3478_;
}
}
case 7:
{
lean_object* v_binderName_3484_; lean_object* v_binderType_3485_; lean_object* v_body_3486_; uint8_t v_binderInfo_3487_; lean_object* v___x_3488_; 
v_binderName_3484_ = lean_ctor_get(v_e_3444_, 0);
lean_inc(v_binderName_3484_);
v_binderType_3485_ = lean_ctor_get(v_e_3444_, 1);
lean_inc_ref(v_binderType_3485_);
v_body_3486_ = lean_ctor_get(v_e_3444_, 2);
lean_inc_ref(v_body_3486_);
v_binderInfo_3487_ = lean_ctor_get_uint8(v_e_3444_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3444_, 3);
lean_inc_ref(v_a_3448_);
lean_inc_ref(v_below_3443_);
lean_inc_ref(v_containsRecFn_3442_);
lean_inc_ref(v_recFnNames_3441_);
lean_inc_ref(v_positions_3440_);
lean_inc_ref(v_recArgInfos_3439_);
v___x_3488_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3439_, v_positions_3440_, v_recFnNames_3441_, v_containsRecFn_3442_, v_below_3443_, v_binderType_3485_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; lean_object* v___f_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = lean_box(v___x_3473_);
v___f_3491_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3491_, 0, v_body_3486_);
lean_closure_set(v___f_3491_, 1, v_recArgInfos_3439_);
lean_closure_set(v___f_3491_, 2, v_positions_3440_);
lean_closure_set(v___f_3491_, 3, v_recFnNames_3441_);
lean_closure_set(v___f_3491_, 4, v_containsRecFn_3442_);
lean_closure_set(v___f_3491_, 5, v_below_3443_);
lean_closure_set(v___f_3491_, 6, v___x_3490_);
lean_closure_set(v___f_3491_, 7, v_a_3465_);
v___x_3492_ = 0;
v___x_3493_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3484_, v_binderInfo_3487_, v_a_3489_, v___f_3491_, v___x_3492_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec_ref(v_a_3448_);
return v___x_3493_;
}
else
{
lean_dec_ref(v_body_3486_);
lean_dec(v_binderName_3484_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
return v___x_3488_;
}
}
case 8:
{
lean_object* v_declName_3494_; lean_object* v_type_3495_; lean_object* v_value_3496_; lean_object* v_body_3497_; uint8_t v_nondep_3498_; lean_object* v___x_3499_; 
lean_dec(v_a_3465_);
v_declName_3494_ = lean_ctor_get(v_e_3444_, 0);
lean_inc(v_declName_3494_);
v_type_3495_ = lean_ctor_get(v_e_3444_, 1);
lean_inc_ref(v_type_3495_);
v_value_3496_ = lean_ctor_get(v_e_3444_, 2);
lean_inc_ref(v_value_3496_);
v_body_3497_ = lean_ctor_get(v_e_3444_, 3);
lean_inc_ref(v_body_3497_);
v_nondep_3498_ = lean_ctor_get_uint8(v_e_3444_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3444_, 4);
lean_inc_ref(v_a_3448_);
lean_inc_ref(v_below_3443_);
lean_inc_ref(v_containsRecFn_3442_);
lean_inc_ref(v_recFnNames_3441_);
lean_inc_ref(v_positions_3440_);
lean_inc_ref(v_recArgInfos_3439_);
v___x_3499_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3439_, v_positions_3440_, v_recFnNames_3441_, v_containsRecFn_3442_, v_below_3443_, v_type_3495_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
lean_inc_ref(v_a_3448_);
lean_inc_ref(v_below_3443_);
lean_inc_ref(v_containsRecFn_3442_);
lean_inc_ref(v_recFnNames_3441_);
lean_inc_ref(v_positions_3440_);
lean_inc_ref(v_recArgInfos_3439_);
v___x_3501_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3439_, v_positions_3440_, v_recFnNames_3441_, v_containsRecFn_3442_, v_below_3443_, v_value_3496_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___f_3503_; uint8_t v___x_3504_; lean_object* v___x_3505_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___f_3503_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3503_, 0, v_body_3497_);
lean_closure_set(v___f_3503_, 1, v_recArgInfos_3439_);
lean_closure_set(v___f_3503_, 2, v_positions_3440_);
lean_closure_set(v___f_3503_, 3, v_recFnNames_3441_);
lean_closure_set(v___f_3503_, 4, v_containsRecFn_3442_);
lean_closure_set(v___f_3503_, 5, v_below_3443_);
v___x_3504_ = 0;
v___x_3505_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3494_, v_a_3500_, v_a_3502_, v___f_3503_, v_nondep_3498_, v___x_3504_, v___x_3473_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec_ref(v_a_3448_);
return v___x_3505_;
}
else
{
lean_dec(v_a_3500_);
lean_dec_ref(v_body_3497_);
lean_dec(v_declName_3494_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
return v___x_3501_;
}
}
else
{
lean_dec_ref(v_body_3497_);
lean_dec_ref(v_value_3496_);
lean_dec(v_declName_3494_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
return v___x_3499_;
}
}
case 10:
{
lean_object* v_data_3506_; lean_object* v_expr_3507_; lean_object* v___x_3508_; 
lean_dec(v_a_3465_);
v_data_3506_ = lean_ctor_get(v_e_3444_, 0);
lean_inc(v_data_3506_);
v_expr_3507_ = lean_ctor_get(v_e_3444_, 1);
lean_inc_ref(v_expr_3507_);
v___x_3508_ = l_Lean_getRecAppSyntax_x3f(v_e_3444_);
lean_dec_ref_known(v_e_3444_, 2);
if (lean_obj_tag(v___x_3508_) == 1)
{
lean_object* v_val_3509_; lean_object* v_fileName_3510_; lean_object* v_fileMap_3511_; lean_object* v_options_3512_; lean_object* v_currRecDepth_3513_; lean_object* v_maxRecDepth_3514_; lean_object* v_ref_3515_; lean_object* v_currNamespace_3516_; lean_object* v_openDecls_3517_; lean_object* v_initHeartbeats_3518_; lean_object* v_maxHeartbeats_3519_; lean_object* v_quotContext_3520_; lean_object* v_currMacroScope_3521_; uint8_t v_diag_3522_; lean_object* v_cancelTk_x3f_3523_; uint8_t v_suppressElabErrors_3524_; lean_object* v_inheritedTraceOptions_3525_; lean_object* v_ref_3526_; lean_object* v___x_3527_; 
lean_dec(v_data_3506_);
v_val_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_val_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v_fileName_3510_ = lean_ctor_get(v_a_3448_, 0);
lean_inc_ref(v_fileName_3510_);
v_fileMap_3511_ = lean_ctor_get(v_a_3448_, 1);
lean_inc_ref(v_fileMap_3511_);
v_options_3512_ = lean_ctor_get(v_a_3448_, 2);
lean_inc_ref(v_options_3512_);
v_currRecDepth_3513_ = lean_ctor_get(v_a_3448_, 3);
lean_inc(v_currRecDepth_3513_);
v_maxRecDepth_3514_ = lean_ctor_get(v_a_3448_, 4);
lean_inc(v_maxRecDepth_3514_);
v_ref_3515_ = lean_ctor_get(v_a_3448_, 5);
lean_inc(v_ref_3515_);
v_currNamespace_3516_ = lean_ctor_get(v_a_3448_, 6);
lean_inc(v_currNamespace_3516_);
v_openDecls_3517_ = lean_ctor_get(v_a_3448_, 7);
lean_inc(v_openDecls_3517_);
v_initHeartbeats_3518_ = lean_ctor_get(v_a_3448_, 8);
lean_inc(v_initHeartbeats_3518_);
v_maxHeartbeats_3519_ = lean_ctor_get(v_a_3448_, 9);
lean_inc(v_maxHeartbeats_3519_);
v_quotContext_3520_ = lean_ctor_get(v_a_3448_, 10);
lean_inc(v_quotContext_3520_);
v_currMacroScope_3521_ = lean_ctor_get(v_a_3448_, 11);
lean_inc(v_currMacroScope_3521_);
v_diag_3522_ = lean_ctor_get_uint8(v_a_3448_, sizeof(void*)*14);
v_cancelTk_x3f_3523_ = lean_ctor_get(v_a_3448_, 12);
lean_inc(v_cancelTk_x3f_3523_);
v_suppressElabErrors_3524_ = lean_ctor_get_uint8(v_a_3448_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3525_ = lean_ctor_get(v_a_3448_, 13);
lean_inc_ref(v_inheritedTraceOptions_3525_);
lean_dec_ref(v_a_3448_);
v_ref_3526_ = l_Lean_replaceRef(v_val_3509_, v_ref_3515_);
lean_dec(v_ref_3515_);
lean_dec(v_val_3509_);
v___x_3527_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3527_, 0, v_fileName_3510_);
lean_ctor_set(v___x_3527_, 1, v_fileMap_3511_);
lean_ctor_set(v___x_3527_, 2, v_options_3512_);
lean_ctor_set(v___x_3527_, 3, v_currRecDepth_3513_);
lean_ctor_set(v___x_3527_, 4, v_maxRecDepth_3514_);
lean_ctor_set(v___x_3527_, 5, v_ref_3526_);
lean_ctor_set(v___x_3527_, 6, v_currNamespace_3516_);
lean_ctor_set(v___x_3527_, 7, v_openDecls_3517_);
lean_ctor_set(v___x_3527_, 8, v_initHeartbeats_3518_);
lean_ctor_set(v___x_3527_, 9, v_maxHeartbeats_3519_);
lean_ctor_set(v___x_3527_, 10, v_quotContext_3520_);
lean_ctor_set(v___x_3527_, 11, v_currMacroScope_3521_);
lean_ctor_set(v___x_3527_, 12, v_cancelTk_x3f_3523_);
lean_ctor_set(v___x_3527_, 13, v_inheritedTraceOptions_3525_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*14, v_diag_3522_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*14 + 1, v_suppressElabErrors_3524_);
v_e_3444_ = v_expr_3507_;
v_a_3448_ = v___x_3527_;
goto _start;
}
else
{
lean_object* v___x_3529_; 
lean_dec(v___x_3508_);
v___x_3529_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3439_, v_positions_3440_, v_recFnNames_3441_, v_containsRecFn_3442_, v_below_3443_, v_expr_3507_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3538_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3532_ = v___x_3529_;
v_isShared_3533_ = v_isSharedCheck_3538_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3529_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3538_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3534_ = l_Lean_mkMData(v_data_3506_, v_a_3530_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3534_);
v___x_3536_ = v___x_3532_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
lean_dec(v_data_3506_);
return v___x_3529_;
}
}
}
case 11:
{
lean_object* v_typeName_3539_; lean_object* v_idx_3540_; lean_object* v_struct_3541_; lean_object* v___x_3542_; 
lean_dec(v_a_3465_);
v_typeName_3539_ = lean_ctor_get(v_e_3444_, 0);
lean_inc(v_typeName_3539_);
v_idx_3540_ = lean_ctor_get(v_e_3444_, 1);
lean_inc(v_idx_3540_);
v_struct_3541_ = lean_ctor_get(v_e_3444_, 2);
lean_inc_ref(v_struct_3541_);
lean_dec_ref_known(v_e_3444_, 3);
v___x_3542_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3439_, v_positions_3440_, v_recFnNames_3441_, v_containsRecFn_3442_, v_below_3443_, v_struct_3541_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3551_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3545_ = v___x_3542_;
v_isShared_3546_ = v_isSharedCheck_3551_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3542_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3551_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3547_ = l_Lean_mkProj(v_typeName_3539_, v_idx_3540_, v_a_3543_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3547_);
v___x_3549_ = v___x_3545_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
else
{
lean_dec(v_idx_3540_);
lean_dec(v_typeName_3539_);
return v___x_3542_;
}
}
case 5:
{
uint8_t v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = lean_unbox(v_a_3465_);
lean_inc_ref(v_e_3444_);
v___x_3553_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3444_, v___x_3552_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
if (lean_obj_tag(v_a_3554_) == 0)
{
lean_dec(v_a_3465_);
v_e_3452_ = v_e_3444_;
v___y_3453_ = v_a_3445_;
v___y_3454_ = v_a_3446_;
v___y_3455_ = v_a_3447_;
v___y_3456_ = v_a_3448_;
v___y_3457_ = v_a_3449_;
goto v___jp_3451_;
}
else
{
lean_object* v_val_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v_val_3555_ = lean_ctor_get(v_a_3554_, 0);
lean_inc(v_val_3555_);
lean_dec_ref_known(v_a_3554_, 1);
v___x_3556_ = lean_unsigned_to_nat(0u);
v___x_3557_ = lean_array_get_size(v_recArgInfos_3439_);
v___x_3558_ = lean_nat_dec_lt(v___x_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_dec(v_val_3555_);
lean_dec(v_a_3465_);
v_e_3452_ = v_e_3444_;
v___y_3453_ = v_a_3445_;
v___y_3454_ = v_a_3446_;
v___y_3455_ = v_a_3447_;
v___y_3456_ = v_a_3448_;
v___y_3457_ = v_a_3449_;
goto v___jp_3451_;
}
else
{
if (v___x_3558_ == 0)
{
lean_dec(v_val_3555_);
lean_dec(v_a_3465_);
v_e_3452_ = v_e_3444_;
v___y_3453_ = v_a_3445_;
v___y_3454_ = v_a_3446_;
v___y_3455_ = v_a_3447_;
v___y_3456_ = v_a_3448_;
v___y_3457_ = v_a_3449_;
goto v___jp_3451_;
}
else
{
size_t v___x_3559_; size_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3559_ = ((size_t)0ULL);
v___x_3560_ = lean_usize_of_nat(v___x_3557_);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3444_, v_recArgInfos_3439_, v___x_3559_, v___x_3560_);
if (v___x_3561_ == 0)
{
lean_dec(v_val_3555_);
lean_dec(v_a_3465_);
v_e_3452_ = v_e_3444_;
v___y_3453_ = v_a_3445_;
v___y_3454_ = v_a_3446_;
v___y_3455_ = v_a_3447_;
v___y_3456_ = v_a_3448_;
v___y_3457_ = v_a_3449_;
goto v___jp_3451_;
}
else
{
lean_object* v_inheritedTraceOptions_3562_; lean_object* v___x_3563_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___x_3633_; 
v_inheritedTraceOptions_3562_ = lean_ctor_get(v_a_3448_, 13);
v___x_3563_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3633_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3563_, v_inheritedTraceOptions_3562_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; uint8_t v___x_3635_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___x_3635_ = lean_unbox(v_a_3634_);
lean_dec(v_a_3634_);
if (v___x_3635_ == 0)
{
v___y_3565_ = v_a_3445_;
v___y_3566_ = v_a_3446_;
v___y_3567_ = v_a_3447_;
v___y_3568_ = v_a_3448_;
v___y_3569_ = v_a_3449_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3636_; 
lean_inc(v_a_3449_);
lean_inc_ref(v_a_3448_);
lean_inc(v_a_3447_);
lean_inc_ref(v_a_3446_);
lean_inc_ref(v_below_3443_);
v___x_3636_ = lean_infer_type(v_below_3443_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3443_);
v___x_3639_ = l_Lean_MessageData_ofExpr(v_below_3443_);
v___x_3640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3638_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
v___x_3641_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = l_Lean_MessageData_ofExpr(v_a_3637_);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3563_, v___x_3644_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_dec_ref_known(v___x_3645_, 1);
v___y_3565_ = v_a_3445_;
v___y_3566_ = v_a_3446_;
v___y_3567_ = v_a_3447_;
v___y_3568_ = v_a_3448_;
v___y_3569_ = v_a_3449_;
goto v___jp_3564_;
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec(v_val_3555_);
lean_dec_ref_known(v_e_3444_, 2);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
else
{
lean_dec(v_val_3555_);
lean_dec_ref_known(v_e_3444_, 2);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
return v___x_3636_;
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec(v_val_3555_);
lean_dec_ref_known(v_e_3444_, 2);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
v_a_3654_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3633_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3633_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
v___jp_3564_:
{
lean_object* v___x_3570_; 
lean_inc_ref(v_below_3443_);
v___x_3570_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3555_, v_below_3443_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
if (lean_obj_tag(v_a_3571_) == 1)
{
lean_object* v_val_3572_; lean_object* v_toMatcherInfo_3573_; lean_object* v_matcherName_3574_; lean_object* v_matcherLevels_3575_; lean_object* v_params_3576_; lean_object* v_motive_3577_; lean_object* v_discrs_3578_; lean_object* v_alts_3579_; lean_object* v_remaining_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; lean_object* v___x_3584_; 
lean_dec_ref(v_below_3443_);
v_val_3572_ = lean_ctor_get(v_a_3571_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v_a_3571_, 1);
v_toMatcherInfo_3573_ = lean_ctor_get(v_val_3572_, 0);
lean_inc_ref(v_toMatcherInfo_3573_);
v_matcherName_3574_ = lean_ctor_get(v_val_3572_, 1);
lean_inc(v_matcherName_3574_);
v_matcherLevels_3575_ = lean_ctor_get(v_val_3572_, 2);
lean_inc_ref(v_matcherLevels_3575_);
v_params_3576_ = lean_ctor_get(v_val_3572_, 3);
lean_inc_ref(v_params_3576_);
v_motive_3577_ = lean_ctor_get(v_val_3572_, 4);
lean_inc_ref(v_motive_3577_);
v_discrs_3578_ = lean_ctor_get(v_val_3572_, 5);
lean_inc_ref(v_discrs_3578_);
v_alts_3579_ = lean_ctor_get(v_val_3572_, 6);
lean_inc_ref(v_alts_3579_);
v_remaining_3580_ = lean_ctor_get(v_val_3572_, 7);
lean_inc_ref(v_remaining_3580_);
v___x_3581_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3572_);
v___x_3582_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3583_ = lean_unbox(v_a_3465_);
lean_dec(v_a_3465_);
v___x_3584_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3439_, v_positions_3440_, v_recFnNames_3441_, v_containsRecFn_3442_, v___x_3583_, v_e_3444_, v_alts_3579_, v___x_3581_, v___x_3556_, v___x_3582_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v_alts_3579_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3594_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3587_ = v___x_3584_;
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3584_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3589_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3589_, 0, v_toMatcherInfo_3573_);
lean_ctor_set(v___x_3589_, 1, v_matcherName_3574_);
lean_ctor_set(v___x_3589_, 2, v_matcherLevels_3575_);
lean_ctor_set(v___x_3589_, 3, v_params_3576_);
lean_ctor_set(v___x_3589_, 4, v_motive_3577_);
lean_ctor_set(v___x_3589_, 5, v_discrs_3578_);
lean_ctor_set(v___x_3589_, 6, v_a_3585_);
lean_ctor_set(v___x_3589_, 7, v_remaining_3580_);
v___x_3590_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3589_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v___x_3590_);
v___x_3592_ = v___x_3587_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref(v_remaining_3580_);
lean_dec_ref(v_discrs_3578_);
lean_dec_ref(v_motive_3577_);
lean_dec_ref(v_params_3576_);
lean_dec_ref(v_matcherLevels_3575_);
lean_dec(v_matcherName_3574_);
lean_dec_ref(v_toMatcherInfo_3573_);
v_a_3595_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3584_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3584_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3603_; lean_object* v___x_3604_; 
lean_dec(v_a_3571_);
lean_dec(v_a_3465_);
v_inheritedTraceOptions_3603_ = lean_ctor_get(v___y_3568_, 13);
v___x_3604_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3563_, v_inheritedTraceOptions_3603_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; uint8_t v___x_3606_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref_known(v___x_3604_, 1);
v___x_3606_ = lean_unbox(v_a_3605_);
lean_dec(v_a_3605_);
if (v___x_3606_ == 0)
{
v_e_3452_ = v_e_3444_;
v___y_3453_ = v___y_3565_;
v___y_3454_ = v___y_3566_;
v___y_3455_ = v___y_3567_;
v___y_3456_ = v___y_3568_;
v___y_3457_ = v___y_3569_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3608_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3563_, v___x_3607_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_dec_ref_known(v___x_3608_, 1);
v_e_3452_ = v_e_3444_;
v___y_3453_ = v___y_3565_;
v___y_3454_ = v___y_3566_;
v___y_3455_ = v___y_3567_;
v___y_3456_ = v___y_3568_;
v___y_3457_ = v___y_3569_;
goto v___jp_3451_;
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec_ref(v___y_3568_);
lean_dec_ref_known(v_e_3444_, 2);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3608_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3608_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref(v___y_3568_);
lean_dec_ref_known(v_e_3444_, 2);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
v_a_3617_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3604_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3604_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref(v___y_3568_);
lean_dec_ref_known(v_e_3444_, 2);
lean_dec(v_a_3465_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
v_a_3625_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3570_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3570_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
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
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec_ref_known(v_e_3444_, 2);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
v_a_3662_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3553_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3553_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
default: 
{
lean_object* v___x_3670_; 
lean_dec(v_a_3465_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
lean_inc_ref(v_e_3444_);
v___x_3670_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3441_, v_e_3444_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec_ref(v_a_3448_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v___x_3670_, 0);
lean_dec(v_unused_3678_);
v___x_3672_ = v___x_3670_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v___x_3670_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_e_3444_);
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_e_3444_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec_ref(v_e_3444_);
v_a_3679_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3670_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3670_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
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
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_e_3444_);
lean_dec_ref(v_below_3443_);
lean_dec_ref(v_containsRecFn_3442_);
lean_dec_ref(v_recFnNames_3441_);
lean_dec_ref(v_positions_3440_);
lean_dec_ref(v_recArgInfos_3439_);
v_a_3688_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3464_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3464_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
v___jp_3451_:
{
lean_object* v_dummy_3458_; lean_object* v_nargs_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v_dummy_3458_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3459_ = l_Lean_Expr_getAppNumArgs(v_e_3452_);
lean_inc(v_nargs_3459_);
v___x_3460_ = lean_mk_array(v_nargs_3459_, v_dummy_3458_);
v___x_3461_ = lean_unsigned_to_nat(1u);
v___x_3462_ = lean_nat_sub(v_nargs_3459_, v___x_3461_);
lean_dec(v_nargs_3459_);
lean_inc_ref(v_e_3452_);
v___x_3463_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3439_, v_positions_3440_, v_recFnNames_3441_, v_containsRecFn_3442_, v_below_3443_, v_e_3452_, v_e_3452_, v___x_3460_, v___x_3462_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec_ref(v___y_3456_);
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3696_, lean_object* v_recArgInfos_3697_, lean_object* v_positions_3698_, lean_object* v_recFnNames_3699_, lean_object* v_containsRecFn_3700_, lean_object* v_below_3701_, lean_object* v_x_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = lean_expr_instantiate1(v_body_3696_, v_x_3702_);
lean_inc_ref(v___y_3706_);
v___x_3710_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3697_, v_positions_3698_, v_recFnNames_3699_, v_containsRecFn_3700_, v_below_3701_, v___x_3709_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3711_, lean_object* v_positions_3712_, lean_object* v_recFnNames_3713_, lean_object* v_containsRecFn_3714_, lean_object* v_below_3715_, lean_object* v_sz_3716_, lean_object* v_i_3717_, lean_object* v_bs_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
size_t v_sz_boxed_3725_; size_t v_i_boxed_3726_; lean_object* v_res_3727_; 
v_sz_boxed_3725_ = lean_unbox_usize(v_sz_3716_);
lean_dec(v_sz_3716_);
v_i_boxed_3726_ = lean_unbox_usize(v_i_3717_);
lean_dec(v_i_3717_);
v_res_3727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3711_, v_positions_3712_, v_recFnNames_3713_, v_containsRecFn_3714_, v_below_3715_, v_sz_boxed_3725_, v_i_boxed_3726_, v_bs_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3728_, lean_object* v_positions_3729_, lean_object* v_recFnNames_3730_, lean_object* v_containsRecFn_3731_, lean_object* v_a_3732_, lean_object* v_e_3733_, lean_object* v_as_3734_, lean_object* v_bs_3735_, lean_object* v_i_3736_, lean_object* v_cs_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
uint8_t v_a_32864__boxed_3744_; lean_object* v_res_3745_; 
v_a_32864__boxed_3744_ = lean_unbox(v_a_3732_);
v_res_3745_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3728_, v_positions_3729_, v_recFnNames_3730_, v_containsRecFn_3731_, v_a_32864__boxed_3744_, v_e_3733_, v_as_3734_, v_bs_3735_, v_i_3736_, v_cs_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v_bs_3735_);
lean_dec_ref(v_as_3734_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3746_, lean_object* v_positions_3747_, lean_object* v_recFnNames_3748_, lean_object* v_containsRecFn_3749_, lean_object* v_below_3750_, lean_object* v_e_3751_, lean_object* v_x_3752_, lean_object* v_x_3753_, lean_object* v_x_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3746_, v_positions_3747_, v_recFnNames_3748_, v_containsRecFn_3749_, v_below_3750_, v_e_3751_, v_x_3752_, v_x_3753_, v_x_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3762_, lean_object* v_positions_3763_, lean_object* v_recFnNames_3764_, lean_object* v_containsRecFn_3765_, lean_object* v_below_3766_, lean_object* v_e_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3762_, v_positions_3763_, v_recFnNames_3764_, v_containsRecFn_3765_, v_below_3766_, v_e_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
lean_dec(v_a_3772_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
lean_dec(v_a_3768_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3775_, lean_object* v_msg_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3776_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3784_, lean_object* v_msg_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3784_, v_msg_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3793_, lean_object* v_name_3794_, lean_object* v_type_3795_, lean_object* v_val_3796_, lean_object* v_k_3797_, uint8_t v_nondep_3798_, uint8_t v_kind_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3794_, v_type_3795_, v_val_3796_, v_k_3797_, v_nondep_3798_, v_kind_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3807_, lean_object* v_name_3808_, lean_object* v_type_3809_, lean_object* v_val_3810_, lean_object* v_k_3811_, lean_object* v_nondep_3812_, lean_object* v_kind_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
uint8_t v_nondep_boxed_3820_; uint8_t v_kind_boxed_3821_; lean_object* v_res_3822_; 
v_nondep_boxed_3820_ = lean_unbox(v_nondep_3812_);
v_kind_boxed_3821_ = lean_unbox(v_kind_3813_);
v_res_3822_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3807_, v_name_3808_, v_type_3809_, v_val_3810_, v_k_3811_, v_nondep_boxed_3820_, v_kind_boxed_3821_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3823_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3839_, lean_object* v_msg_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3839_, v_msg_3840_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3848_, lean_object* v_msg_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3848_, v_msg_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3857_, lean_object* v_constName_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3866_, lean_object* v_constName_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3866_, v_constName_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3875_, lean_object* v_ref_3876_, lean_object* v_constName_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3876_, v_constName_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3885_, lean_object* v_ref_3886_, lean_object* v_constName_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3885_, v_ref_3886_, v_constName_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec(v_ref_3886_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3895_, lean_object* v_ref_3896_, lean_object* v_msg_3897_, lean_object* v_declHint_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3896_, v_msg_3897_, v_declHint_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3906_, lean_object* v_ref_3907_, lean_object* v_msg_3908_, lean_object* v_declHint_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3906_, v_ref_3907_, v_msg_3908_, v_declHint_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec(v_ref_3907_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3917_, lean_object* v_declHint_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3917_, v_declHint_3918_, v___y_3923_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3926_, lean_object* v_declHint_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3926_, v_declHint_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3935_, lean_object* v_ref_3936_, lean_object* v_msg_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3936_, v_msg_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3945_, lean_object* v_ref_3946_, lean_object* v_msg_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3945_, v_ref_3946_, v_msg_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec(v_ref_3946_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3955_, lean_object* v_e_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v_fst_3965_; lean_object* v_snd_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3963_ = lean_st_ref_take(v___y_3957_);
v___x_3964_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3955_, v_e_3956_, v___x_3963_);
v_fst_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_fst_3965_);
v_snd_3966_ = lean_ctor_get(v___x_3964_, 1);
lean_inc(v_snd_3966_);
lean_dec_ref(v___x_3964_);
v___x_3967_ = lean_st_ref_set(v___y_3957_, v_snd_3966_);
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v_fst_3965_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3969_, lean_object* v_e_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3969_, v_e_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v_recFnNames_3969_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3978_, size_t v_i_3979_, lean_object* v_bs_3980_){
_start:
{
uint8_t v___x_3981_; 
v___x_3981_ = lean_usize_dec_lt(v_i_3979_, v_sz_3978_);
if (v___x_3981_ == 0)
{
return v_bs_3980_;
}
else
{
lean_object* v_v_3982_; lean_object* v_fnName_3983_; lean_object* v___x_3984_; lean_object* v_bs_x27_3985_; size_t v___x_3986_; size_t v___x_3987_; lean_object* v___x_3988_; 
v_v_3982_ = lean_array_uget_borrowed(v_bs_3980_, v_i_3979_);
v_fnName_3983_ = lean_ctor_get(v_v_3982_, 0);
lean_inc(v_fnName_3983_);
v___x_3984_ = lean_unsigned_to_nat(0u);
v_bs_x27_3985_ = lean_array_uset(v_bs_3980_, v_i_3979_, v___x_3984_);
v___x_3986_ = ((size_t)1ULL);
v___x_3987_ = lean_usize_add(v_i_3979_, v___x_3986_);
v___x_3988_ = lean_array_uset(v_bs_x27_3985_, v_i_3979_, v_fnName_3983_);
v_i_3979_ = v___x_3987_;
v_bs_3980_ = v___x_3988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3990_, lean_object* v_i_3991_, lean_object* v_bs_3992_){
_start:
{
size_t v_sz_boxed_3993_; size_t v_i_boxed_3994_; lean_object* v_res_3995_; 
v_sz_boxed_3993_ = lean_unbox_usize(v_sz_3990_);
lean_dec(v_sz_3990_);
v_i_boxed_3994_ = lean_unbox_usize(v_i_3991_);
lean_dec(v_i_3991_);
v_res_3995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3993_, v_i_boxed_3994_, v_bs_3992_);
return v_res_3995_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3996_ = lean_box(0);
v___x_3997_ = lean_unsigned_to_nat(16u);
v___x_3998_ = lean_mk_array(v___x_3997_, v___x_3996_);
return v___x_3998_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_4000_ = lean_unsigned_to_nat(0u);
v___x_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
lean_ctor_set(v___x_4001_, 1, v___x_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_4002_, lean_object* v_positions_4003_, lean_object* v_below_4004_, lean_object* v_e_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; size_t v_sz_4013_; size_t v___x_4014_; lean_object* v_recFnNames_4015_; lean_object* v_containsRecFn_4016_; lean_object* v___x_4017_; 
v___x_4011_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_4012_ = lean_st_mk_ref(v___x_4011_);
v_sz_4013_ = lean_array_size(v_recArgInfos_4002_);
v___x_4014_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_4002_);
v_recFnNames_4015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_4013_, v___x_4014_, v_recArgInfos_4002_);
lean_inc_ref(v_recFnNames_4015_);
v_containsRecFn_4016_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_4016_, 0, v_recFnNames_4015_);
lean_inc_ref(v_a_4008_);
v___x_4017_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_4002_, v_positions_4003_, v_recFnNames_4015_, v_containsRecFn_4016_, v_below_4004_, v_e_4005_, v___x_4012_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4026_; 
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4020_ = v___x_4017_;
v_isShared_4021_ = v_isSharedCheck_4026_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4026_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4022_ = lean_st_ref_get(v___x_4012_);
lean_dec(v___x_4012_);
lean_dec(v___x_4022_);
if (v_isShared_4021_ == 0)
{
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4018_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
else
{
lean_dec(v___x_4012_);
return v___x_4017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_4027_, lean_object* v_positions_4028_, lean_object* v_below_4029_, lean_object* v_e_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4027_, v_positions_4028_, v_below_4029_, v_e_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_4037_, lean_object* v_k_4038_, uint8_t v_cleanupAnnotations_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v___f_4045_; uint8_t v___x_4046_; uint8_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___f_4045_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4045_, 0, v_k_4038_);
v___x_4046_ = 1;
v___x_4047_ = 0;
v___x_4048_ = lean_box(0);
v___x_4049_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4037_, v___x_4046_, v___x_4047_, v___x_4046_, v___x_4047_, v___x_4048_, v___f_4045_, v_cleanupAnnotations_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
v_a_4058_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4049_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4049_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4066_, lean_object* v_k_4067_, lean_object* v_cleanupAnnotations_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4074_; lean_object* v_res_4075_; 
v_cleanupAnnotations_boxed_4074_ = lean_unbox(v_cleanupAnnotations_4068_);
v_res_4075_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4066_, v_k_4067_, v_cleanupAnnotations_boxed_4074_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4076_, lean_object* v_e_4077_, lean_object* v_k_4078_, uint8_t v_cleanupAnnotations_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4077_, v_k_4078_, v_cleanupAnnotations_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4086_, lean_object* v_e_4087_, lean_object* v_k_4088_, lean_object* v_cleanupAnnotations_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4095_; lean_object* v_res_4096_; 
v_cleanupAnnotations_boxed_4095_ = lean_unbox(v_cleanupAnnotations_4089_);
v_res_4096_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4086_, v_e_4087_, v_k_4088_, v_cleanupAnnotations_boxed_4095_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4097_, lean_object* v_recArgInfo_4098_, lean_object* v_xs_4099_, lean_object* v___value_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l_Lean_Meta_instantiateForall(v_type_4097_, v_xs_4099_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4108_; lean_object* v_fst_4109_; lean_object* v_snd_4110_; uint8_t v___x_4111_; uint8_t v___x_4112_; uint8_t v___x_4113_; lean_object* v___x_4114_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4108_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4098_, v_xs_4099_);
v_fst_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_fst_4109_);
v_snd_4110_ = lean_ctor_get(v___x_4108_, 1);
lean_inc(v_snd_4110_);
lean_dec_ref(v___x_4108_);
v___x_4111_ = 0;
v___x_4112_ = 1;
v___x_4113_ = 1;
v___x_4114_ = l_Lean_Meta_mkForallFVars(v_snd_4110_, v_a_4107_, v___x_4111_, v___x_4112_, v___x_4112_, v___x_4113_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v_snd_4110_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; lean_object* v___x_4116_; 
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4115_);
lean_dec_ref_known(v___x_4114_, 1);
v___x_4116_ = l_Lean_Meta_mkLambdaFVars(v_fst_4109_, v_a_4115_, v___x_4111_, v___x_4112_, v___x_4111_, v___x_4112_, v___x_4113_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v_fst_4109_);
return v___x_4116_;
}
else
{
lean_dec(v_fst_4109_);
return v___x_4114_;
}
}
else
{
lean_dec_ref(v_xs_4099_);
lean_dec_ref(v_recArgInfo_4098_);
return v___x_4106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4117_, lean_object* v_recArgInfo_4118_, lean_object* v_xs_4119_, lean_object* v___value_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4117_, v_recArgInfo_4118_, v_xs_4119_, v___value_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec_ref(v___value_4120_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4127_, lean_object* v_value_4128_, lean_object* v_type_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v___f_4135_; uint8_t v___x_4136_; lean_object* v___x_4137_; 
v___f_4135_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4135_, 0, v_type_4129_);
lean_closure_set(v___f_4135_, 1, v_recArgInfo_4127_);
v___x_4136_ = 0;
v___x_4137_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4128_, v___f_4135_, v___x_4136_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4138_, lean_object* v_value_4139_, lean_object* v_type_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4138_, v_value_4139_, v_type_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4147_, lean_object* v_maxFVars_x3f_4148_, lean_object* v_k_4149_, uint8_t v_cleanupAnnotations_4150_, uint8_t v_whnfType_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v___f_4157_; lean_object* v___x_4158_; 
v___f_4157_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4157_, 0, v_k_4149_);
v___x_4158_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4147_, v_maxFVars_x3f_4148_, v___f_4157_, v_cleanupAnnotations_4150_, v_whnfType_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
v_a_4167_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4158_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4158_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4175_, lean_object* v_maxFVars_x3f_4176_, lean_object* v_k_4177_, lean_object* v_cleanupAnnotations_4178_, lean_object* v_whnfType_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4185_; uint8_t v_whnfType_boxed_4186_; lean_object* v_res_4187_; 
v_cleanupAnnotations_boxed_4185_ = lean_unbox(v_cleanupAnnotations_4178_);
v_whnfType_boxed_4186_ = lean_unbox(v_whnfType_4179_);
v_res_4187_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4175_, v_maxFVars_x3f_4176_, v_k_4177_, v_cleanupAnnotations_boxed_4185_, v_whnfType_boxed_4186_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4188_, lean_object* v_type_4189_, lean_object* v_maxFVars_x3f_4190_, lean_object* v_k_4191_, uint8_t v_cleanupAnnotations_4192_, uint8_t v_whnfType_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4189_, v_maxFVars_x3f_4190_, v_k_4191_, v_cleanupAnnotations_4192_, v_whnfType_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4200_, lean_object* v_type_4201_, lean_object* v_maxFVars_x3f_4202_, lean_object* v_k_4203_, lean_object* v_cleanupAnnotations_4204_, lean_object* v_whnfType_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4211_; uint8_t v_whnfType_boxed_4212_; lean_object* v_res_4213_; 
v_cleanupAnnotations_boxed_4211_ = lean_unbox(v_cleanupAnnotations_4204_);
v_whnfType_boxed_4212_ = lean_unbox(v_whnfType_4205_);
v_res_4213_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4200_, v_type_4201_, v_maxFVars_x3f_4202_, v_k_4203_, v_cleanupAnnotations_boxed_4211_, v_whnfType_boxed_4212_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4214_, lean_object* v_recArgInfos_4215_, lean_object* v_positions_4216_, lean_object* v_value_4217_, lean_object* v_fst_4218_, lean_object* v_snd_4219_, lean_object* v_below_4220_, lean_object* v_x_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4227_ = lean_unsigned_to_nat(0u);
v___x_4228_ = lean_array_get_borrowed(v___x_4214_, v_below_4220_, v___x_4227_);
lean_inc(v___x_4228_);
v___x_4229_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4215_, v_positions_4216_, v___x_4228_, v_value_4217_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; uint8_t v___x_4236_; uint8_t v___x_4237_; uint8_t v___x_4238_; lean_object* v___x_4239_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v___x_4229_, 1);
v___x_4231_ = lean_unsigned_to_nat(1u);
v___x_4232_ = lean_mk_empty_array_with_capacity(v___x_4231_);
lean_inc(v___x_4228_);
v___x_4233_ = lean_array_push(v___x_4232_, v___x_4228_);
v___x_4234_ = l_Array_append___redArg(v_fst_4218_, v___x_4233_);
lean_dec_ref(v___x_4233_);
v___x_4235_ = l_Array_append___redArg(v___x_4234_, v_snd_4219_);
v___x_4236_ = 0;
v___x_4237_ = 1;
v___x_4238_ = 1;
v___x_4239_ = l_Lean_Meta_mkLambdaFVars(v___x_4235_, v_a_4230_, v___x_4236_, v___x_4237_, v___x_4236_, v___x_4237_, v___x_4238_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec_ref(v___x_4235_);
return v___x_4239_;
}
else
{
lean_dec_ref(v_fst_4218_);
return v___x_4229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4240_, lean_object* v_recArgInfos_4241_, lean_object* v_positions_4242_, lean_object* v_value_4243_, lean_object* v_fst_4244_, lean_object* v_snd_4245_, lean_object* v_below_4246_, lean_object* v_x_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4240_, v_recArgInfos_4241_, v_positions_4242_, v_value_4243_, v_fst_4244_, v_snd_4245_, v_below_4246_, v_x_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec_ref(v_x_4247_);
lean_dec_ref(v_below_4246_);
lean_dec_ref(v_snd_4245_);
lean_dec_ref(v___x_4240_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4256_, lean_object* v_FType_4257_, lean_object* v___x_4258_, lean_object* v_recArgInfos_4259_, lean_object* v_positions_4260_, lean_object* v_xs_4261_, lean_object* v_value_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; lean_object* v_fst_4269_; lean_object* v_snd_4270_; lean_object* v___x_4271_; 
v___x_4268_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4256_, v_xs_4261_);
v_fst_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_fst_4269_);
v_snd_4270_ = lean_ctor_get(v___x_4268_, 1);
lean_inc(v_snd_4270_);
lean_dec_ref(v___x_4268_);
v___x_4271_ = l_Lean_Meta_instantiateForall(v_FType_4257_, v_fst_4269_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v_a_4272_; lean_object* v___f_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; 
v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
lean_inc(v_a_4272_);
lean_dec_ref_known(v___x_4271_, 1);
v___f_4273_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4273_, 0, v___x_4258_);
lean_closure_set(v___f_4273_, 1, v_recArgInfos_4259_);
lean_closure_set(v___f_4273_, 2, v_positions_4260_);
lean_closure_set(v___f_4273_, 3, v_value_4262_);
lean_closure_set(v___f_4273_, 4, v_fst_4269_);
lean_closure_set(v___f_4273_, 5, v_snd_4270_);
v___x_4274_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4275_ = 0;
v___x_4276_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4272_, v___x_4274_, v___f_4273_, v___x_4275_, v___x_4275_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
return v___x_4276_;
}
else
{
lean_dec(v_snd_4270_);
lean_dec(v_fst_4269_);
lean_dec_ref(v_value_4262_);
lean_dec_ref(v_positions_4260_);
lean_dec_ref(v_recArgInfos_4259_);
lean_dec_ref(v___x_4258_);
return v___x_4271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4277_, lean_object* v_FType_4278_, lean_object* v___x_4279_, lean_object* v_recArgInfos_4280_, lean_object* v_positions_4281_, lean_object* v_xs_4282_, lean_object* v_value_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4277_, v_FType_4278_, v___x_4279_, v_recArgInfos_4280_, v_positions_4281_, v_xs_4282_, v_value_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4290_, lean_object* v_positions_4291_, lean_object* v_recArgInfo_4292_, lean_object* v_value_4293_, lean_object* v_FType_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v___x_4300_; lean_object* v___f_4301_; uint8_t v___x_4302_; lean_object* v___x_4303_; 
v___x_4300_ = l_Lean_instInhabitedExpr;
v___f_4301_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4301_, 0, v_recArgInfo_4292_);
lean_closure_set(v___f_4301_, 1, v_FType_4294_);
lean_closure_set(v___f_4301_, 2, v___x_4300_);
lean_closure_set(v___f_4301_, 3, v_recArgInfos_4290_);
lean_closure_set(v___f_4301_, 4, v_positions_4291_);
v___x_4302_ = 0;
v___x_4303_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4293_, v___f_4301_, v___x_4302_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4304_, lean_object* v_positions_4305_, lean_object* v_recArgInfo_4306_, lean_object* v_value_4307_, lean_object* v_FType_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4304_, v_positions_4305_, v_recArgInfo_4306_, v_value_4307_, v_FType_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4315_, lean_object* v_params_4316_, uint8_t v_isIndPred_4317_, lean_object* v_brecOnUniv_4318_, lean_object* v_levels_4319_, lean_object* v_idx_4320_){
_start:
{
lean_object* v_n_4321_; lean_object* v___y_4323_; 
v_n_4321_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4315_, v_idx_4320_);
if (v_isIndPred_4317_ == 0)
{
lean_object* v___x_4326_; 
v___x_4326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4326_, 0, v_brecOnUniv_4318_);
lean_ctor_set(v___x_4326_, 1, v_levels_4319_);
v___y_4323_ = v___x_4326_;
goto v___jp_4322_;
}
else
{
lean_dec(v_brecOnUniv_4318_);
v___y_4323_ = v_levels_4319_;
goto v___jp_4322_;
}
v___jp_4322_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = l_Lean_Expr_const___override(v_n_4321_, v___y_4323_);
v___x_4325_ = l_Lean_mkAppN(v___x_4324_, v_params_4316_);
return v___x_4325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4327_, lean_object* v_params_4328_, lean_object* v_isIndPred_4329_, lean_object* v_brecOnUniv_4330_, lean_object* v_levels_4331_, lean_object* v_idx_4332_){
_start:
{
uint8_t v_isIndPred_boxed_4333_; lean_object* v_res_4334_; 
v_isIndPred_boxed_4333_ = lean_unbox(v_isIndPred_4329_);
v_res_4334_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4327_, v_params_4328_, v_isIndPred_boxed_4333_, v_brecOnUniv_4330_, v_levels_4331_, v_idx_4332_);
lean_dec(v_idx_4332_);
lean_dec_ref(v_params_4328_);
lean_dec_ref(v_toIndGroupInfo_4327_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4335_, lean_object* v_a_4336_, lean_object* v_n_4337_){
_start:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = lean_apply_1(v_brecOnCons_4335_, v_n_4337_);
v___x_4339_ = l_Lean_mkAppN(v___x_4338_, v_a_4336_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4340_, lean_object* v_a_4341_, lean_object* v_n_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4340_, v_a_4341_, v_n_4342_);
lean_dec_ref(v_a_4341_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4344_, lean_object* v_type_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Lean_Meta_getLevel(v_type_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4352_, lean_object* v_type_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4352_, v_type_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec_ref(v_x_4352_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4360_, size_t v_sz_4361_, size_t v_i_4362_, lean_object* v_bs_4363_){
_start:
{
uint8_t v___x_4364_; 
v___x_4364_ = lean_usize_dec_lt(v_i_4362_, v_sz_4361_);
if (v___x_4364_ == 0)
{
return v_bs_4363_;
}
else
{
lean_object* v___x_4365_; lean_object* v_v_4366_; lean_object* v___x_4367_; lean_object* v_bs_x27_4368_; lean_object* v___x_4369_; size_t v___x_4370_; size_t v___x_4371_; lean_object* v___x_4372_; 
v___x_4365_ = l_Lean_instInhabitedExpr;
v_v_4366_ = lean_array_uget(v_bs_4363_, v_i_4362_);
v___x_4367_ = lean_unsigned_to_nat(0u);
v_bs_x27_4368_ = lean_array_uset(v_bs_4363_, v_i_4362_, v___x_4367_);
v___x_4369_ = lean_array_get_borrowed(v___x_4365_, v_xs_4360_, v_v_4366_);
lean_dec(v_v_4366_);
v___x_4370_ = ((size_t)1ULL);
v___x_4371_ = lean_usize_add(v_i_4362_, v___x_4370_);
lean_inc(v___x_4369_);
v___x_4372_ = lean_array_uset(v_bs_x27_4368_, v_i_4362_, v___x_4369_);
v_i_4362_ = v___x_4371_;
v_bs_4363_ = v___x_4372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4374_, lean_object* v_sz_4375_, lean_object* v_i_4376_, lean_object* v_bs_4377_){
_start:
{
size_t v_sz_boxed_4378_; size_t v_i_boxed_4379_; lean_object* v_res_4380_; 
v_sz_boxed_4378_ = lean_unbox_usize(v_sz_4375_);
lean_dec(v_sz_4375_);
v_i_boxed_4379_ = lean_unbox_usize(v_i_4376_);
lean_dec(v_i_4376_);
v_res_4380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4374_, v_sz_boxed_4378_, v_i_boxed_4379_, v_bs_4377_);
lean_dec_ref(v_xs_4374_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4381_, lean_object* v_f_4382_, lean_object* v_as_4383_, lean_object* v_bs_4384_, lean_object* v_i_4385_, lean_object* v_cs_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___x_4392_; uint8_t v___x_4393_; 
v___x_4392_ = lean_array_get_size(v_as_4383_);
v___x_4393_ = lean_nat_dec_lt(v_i_4385_, v___x_4392_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4394_; 
lean_dec(v_i_4385_);
lean_dec_ref(v_f_4382_);
v___x_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4394_, 0, v_cs_4386_);
return v___x_4394_;
}
else
{
lean_object* v___x_4395_; uint8_t v___x_4396_; 
v___x_4395_ = lean_array_get_size(v_bs_4384_);
v___x_4396_ = lean_nat_dec_lt(v_i_4385_, v___x_4395_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4397_; 
lean_dec(v_i_4385_);
lean_dec_ref(v_f_4382_);
v___x_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4397_, 0, v_cs_4386_);
return v___x_4397_;
}
else
{
lean_object* v_a_4398_; lean_object* v_b_4399_; size_t v_sz_4400_; size_t v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_a_4398_ = lean_array_fget_borrowed(v_as_4383_, v_i_4385_);
v_b_4399_ = lean_array_fget_borrowed(v_bs_4384_, v_i_4385_);
v_sz_4400_ = lean_array_size(v_b_4399_);
v___x_4401_ = ((size_t)0ULL);
lean_inc(v_b_4399_);
v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4381_, v_sz_4400_, v___x_4401_, v_b_4399_);
lean_inc_ref(v_f_4382_);
lean_inc(v___y_4390_);
lean_inc_ref(v___y_4389_);
lean_inc(v___y_4388_);
lean_inc_ref(v___y_4387_);
lean_inc(v_a_4398_);
v___x_4403_ = lean_apply_7(v_f_4382_, v_a_4398_, v___x_4402_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, lean_box(0));
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = lean_unsigned_to_nat(1u);
v___x_4406_ = lean_nat_add(v_i_4385_, v___x_4405_);
lean_dec(v_i_4385_);
v___x_4407_ = lean_array_push(v_cs_4386_, v_a_4404_);
v_i_4385_ = v___x_4406_;
v_cs_4386_ = v___x_4407_;
goto _start;
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec_ref(v_cs_4386_);
lean_dec(v_i_4385_);
lean_dec_ref(v_f_4382_);
v_a_4409_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4403_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4403_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4417_, lean_object* v_f_4418_, lean_object* v_as_4419_, lean_object* v_bs_4420_, lean_object* v_i_4421_, lean_object* v_cs_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4417_, v_f_4418_, v_as_4419_, v_bs_4420_, v_i_4421_, v_cs_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec_ref(v_bs_4420_);
lean_dec_ref(v_as_4419_);
lean_dec_ref(v_xs_4417_);
return v_res_4428_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l_Array_instInhabited(lean_box(0));
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v___x_4436_; lean_object* v_toApplicative_4437_; lean_object* v_toFunctor_4438_; lean_object* v_toSeq_4439_; lean_object* v_toSeqLeft_4440_; lean_object* v_toSeqRight_4441_; lean_object* v___f_4442_; lean_object* v___f_4443_; lean_object* v___f_4444_; lean_object* v___f_4445_; lean_object* v___x_4446_; lean_object* v___f_4447_; lean_object* v___f_4448_; lean_object* v___f_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v_toApplicative_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4484_; 
v___x_4436_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4437_ = lean_ctor_get(v___x_4436_, 0);
v_toFunctor_4438_ = lean_ctor_get(v_toApplicative_4437_, 0);
v_toSeq_4439_ = lean_ctor_get(v_toApplicative_4437_, 2);
v_toSeqLeft_4440_ = lean_ctor_get(v_toApplicative_4437_, 3);
v_toSeqRight_4441_ = lean_ctor_get(v_toApplicative_4437_, 4);
v___f_4442_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4443_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4438_, 2);
v___f_4444_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4444_, 0, v_toFunctor_4438_);
v___f_4445_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4445_, 0, v_toFunctor_4438_);
v___x_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___f_4444_);
lean_ctor_set(v___x_4446_, 1, v___f_4445_);
lean_inc(v_toSeqRight_4441_);
v___f_4447_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4447_, 0, v_toSeqRight_4441_);
lean_inc(v_toSeqLeft_4440_);
v___f_4448_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4448_, 0, v_toSeqLeft_4440_);
lean_inc(v_toSeq_4439_);
v___f_4449_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4449_, 0, v_toSeq_4439_);
v___x_4450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4446_);
lean_ctor_set(v___x_4450_, 1, v___f_4442_);
lean_ctor_set(v___x_4450_, 2, v___f_4449_);
lean_ctor_set(v___x_4450_, 3, v___f_4448_);
lean_ctor_set(v___x_4450_, 4, v___f_4447_);
v___x_4451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
lean_ctor_set(v___x_4451_, 1, v___f_4443_);
v___x_4452_ = l_StateRefT_x27_instMonad___redArg(v___x_4451_);
v_toApplicative_4453_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4484_ == 0)
{
lean_object* v_unused_4485_; 
v_unused_4485_ = lean_ctor_get(v___x_4452_, 1);
lean_dec(v_unused_4485_);
v___x_4455_ = v___x_4452_;
v_isShared_4456_ = v_isSharedCheck_4484_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_toApplicative_4453_);
lean_dec(v___x_4452_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4484_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v_toFunctor_4457_; lean_object* v_toSeq_4458_; lean_object* v_toSeqLeft_4459_; lean_object* v_toSeqRight_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4482_; 
v_toFunctor_4457_ = lean_ctor_get(v_toApplicative_4453_, 0);
v_toSeq_4458_ = lean_ctor_get(v_toApplicative_4453_, 2);
v_toSeqLeft_4459_ = lean_ctor_get(v_toApplicative_4453_, 3);
v_toSeqRight_4460_ = lean_ctor_get(v_toApplicative_4453_, 4);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_toApplicative_4453_);
if (v_isSharedCheck_4482_ == 0)
{
lean_object* v_unused_4483_; 
v_unused_4483_ = lean_ctor_get(v_toApplicative_4453_, 1);
lean_dec(v_unused_4483_);
v___x_4462_ = v_toApplicative_4453_;
v_isShared_4463_ = v_isSharedCheck_4482_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_toSeqRight_4460_);
lean_inc(v_toSeqLeft_4459_);
lean_inc(v_toSeq_4458_);
lean_inc(v_toFunctor_4457_);
lean_dec(v_toApplicative_4453_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4482_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___f_4464_; lean_object* v___f_4465_; lean_object* v___f_4466_; lean_object* v___f_4467_; lean_object* v___x_4468_; lean_object* v___f_4469_; lean_object* v___f_4470_; lean_object* v___f_4471_; lean_object* v___x_4473_; 
v___f_4464_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4465_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4457_);
v___f_4466_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4466_, 0, v_toFunctor_4457_);
v___f_4467_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4467_, 0, v_toFunctor_4457_);
v___x_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___f_4466_);
lean_ctor_set(v___x_4468_, 1, v___f_4467_);
v___f_4469_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4469_, 0, v_toSeqRight_4460_);
v___f_4470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4470_, 0, v_toSeqLeft_4459_);
v___f_4471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4471_, 0, v_toSeq_4458_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 4, v___f_4469_);
lean_ctor_set(v___x_4462_, 3, v___f_4470_);
lean_ctor_set(v___x_4462_, 2, v___f_4471_);
lean_ctor_set(v___x_4462_, 1, v___f_4464_);
lean_ctor_set(v___x_4462_, 0, v___x_4468_);
v___x_4473_ = v___x_4462_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v___f_4464_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v___f_4471_);
lean_ctor_set(v_reuseFailAlloc_4481_, 3, v___f_4470_);
lean_ctor_set(v_reuseFailAlloc_4481_, 4, v___f_4469_);
v___x_4473_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
lean_object* v___x_4475_; 
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 1, v___f_4465_);
lean_ctor_set(v___x_4455_, 0, v___x_4473_);
v___x_4475_ = v___x_4455_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v___f_4465_);
v___x_4475_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_940__overap_4478_; lean_object* v___x_4479_; 
v___x_4476_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4477_ = l_instInhabitedOfMonad___redArg(v___x_4475_, v___x_4476_);
v___x_940__overap_4478_ = lean_panic_fn_borrowed(v___x_4477_, v_msg_4430_);
lean_dec(v___x_4477_);
lean_inc(v___y_4434_);
lean_inc_ref(v___y_4433_);
lean_inc(v___y_4432_);
lean_inc_ref(v___y_4431_);
v___x_4479_ = lean_apply_5(v___x_940__overap_4478_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, lean_box(0));
return v___x_4479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
return v_res_4492_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4496_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4497_ = lean_unsigned_to_nat(2u);
v___x_4498_ = lean_unsigned_to_nat(73u);
v___x_4499_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4500_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4501_ = l_mkPanicMessageWithDecl(v___x_4500_, v___x_4499_, v___x_4498_, v___x_4497_, v___x_4496_);
return v___x_4501_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4503_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4504_ = lean_unsigned_to_nat(2u);
v___x_4505_ = lean_unsigned_to_nat(74u);
v___x_4506_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4507_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4508_ = l_mkPanicMessageWithDecl(v___x_4507_, v___x_4506_, v___x_4505_, v___x_4504_, v___x_4503_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4511_, lean_object* v_positions_4512_, lean_object* v_ys_4513_, lean_object* v_xs_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4520_ = lean_array_get_size(v_positions_4512_);
v___x_4521_ = lean_array_get_size(v_ys_4513_);
v___x_4522_ = lean_nat_dec_eq(v___x_4520_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
lean_dec_ref(v_f_4511_);
v___x_4523_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4524_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4523_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
return v___x_4524_;
}
else
{
lean_object* v___x_4525_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4525_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4512_);
v___x_4526_ = lean_array_get_size(v_xs_4514_);
v___x_4527_ = lean_nat_dec_eq(v___x_4525_, v___x_4526_);
lean_dec(v___x_4525_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
lean_dec_ref(v_f_4511_);
v___x_4528_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4529_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4528_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
return v___x_4529_;
}
else
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4530_ = lean_unsigned_to_nat(0u);
v___x_4531_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4532_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4514_, v_f_4511_, v_ys_4513_, v_positions_4512_, v___x_4530_, v___x_4531_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
return v___x_4532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4533_, lean_object* v_positions_4534_, lean_object* v_ys_4535_, lean_object* v_xs_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4533_, v_positions_4534_, v_ys_4535_, v_xs_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec_ref(v_xs_4536_);
lean_dec_ref(v_ys_4535_);
lean_dec_ref(v_positions_4534_);
return v_res_4542_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = lean_unsigned_to_nat(0u);
v___x_4545_ = l_Lean_Level_ofNat(v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4546_, lean_object* v_positions_4547_, lean_object* v_motives_4548_, uint8_t v_isIndPred_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v_indGroupInst_4558_; lean_object* v_brecOnUniv_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; 
v___x_4555_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4556_ = lean_unsigned_to_nat(0u);
v___x_4557_ = lean_array_get_borrowed(v___x_4555_, v_recArgInfos_4546_, v___x_4556_);
v_indGroupInst_4558_ = lean_ctor_get(v___x_4557_, 4);
if (v_isIndPred_4549_ == 0)
{
lean_object* v___f_4601_; lean_object* v___x_4602_; lean_object* v_motive_4603_; lean_object* v___x_4604_; 
v___f_4601_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4602_ = l_Lean_instInhabitedExpr;
v_motive_4603_ = lean_array_get_borrowed(v___x_4602_, v_motives_4548_, v___x_4556_);
lean_inc(v_motive_4603_);
v___x_4604_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4603_, v___f_4601_, v_isIndPred_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref_known(v___x_4604_, 1);
v_brecOnUniv_4560_ = v_a_4605_;
v___y_4561_ = v_a_4550_;
v___y_4562_ = v_a_4551_;
v___y_4563_ = v_a_4552_;
v___y_4564_ = v_a_4553_;
goto v___jp_4559_;
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
v_a_4606_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4604_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4604_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
else
{
lean_object* v___x_4614_; 
v___x_4614_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4560_ = v___x_4614_;
v___y_4561_ = v_a_4550_;
v___y_4562_ = v_a_4551_;
v___y_4563_ = v_a_4552_;
v___y_4564_ = v_a_4553_;
goto v___jp_4559_;
}
v___jp_4559_:
{
lean_object* v_toIndGroupInfo_4565_; lean_object* v_levels_4566_; lean_object* v_params_4567_; lean_object* v___x_4568_; lean_object* v_brecOnCons_4569_; lean_object* v_brecOnAux_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v_toIndGroupInfo_4565_ = lean_ctor_get(v_indGroupInst_4558_, 0);
v_levels_4566_ = lean_ctor_get(v_indGroupInst_4558_, 1);
v_params_4567_ = lean_ctor_get(v_indGroupInst_4558_, 2);
v___x_4568_ = lean_box(v_isIndPred_4549_);
lean_inc_n(v_levels_4566_, 2);
lean_inc(v_brecOnUniv_4560_);
lean_inc_ref(v_params_4567_);
lean_inc_ref(v_toIndGroupInfo_4565_);
v_brecOnCons_4569_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4569_, 0, v_toIndGroupInfo_4565_);
lean_closure_set(v_brecOnCons_4569_, 1, v_params_4567_);
lean_closure_set(v_brecOnCons_4569_, 2, v___x_4568_);
lean_closure_set(v_brecOnCons_4569_, 3, v_brecOnUniv_4560_);
lean_closure_set(v_brecOnCons_4569_, 4, v_levels_4566_);
v_brecOnAux_4570_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4565_, v_params_4567_, v_isIndPred_4549_, v_brecOnUniv_4560_, v_levels_4566_, v___x_4556_);
v___x_4571_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4565_);
v___x_4572_ = l_Lean_Meta_inferArgumentTypesN(v___x_4571_, v_brecOnAux_4570_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4572_, 1);
v___x_4574_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4575_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4574_, v_positions_4547_, v_a_4573_, v_motives_4548_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v_a_4573_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4584_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4578_ = v___x_4575_;
v_isShared_4579_ = v_isSharedCheck_4584_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4575_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4584_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___f_4580_; lean_object* v___x_4582_; 
v___f_4580_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4580_, 0, v_brecOnCons_4569_);
lean_closure_set(v___f_4580_, 1, v_a_4576_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v___f_4580_);
v___x_4582_ = v___x_4578_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___f_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_brecOnCons_4569_);
v_a_4585_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4575_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4575_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec_ref(v_brecOnCons_4569_);
v_a_4593_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4572_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4572_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4615_, lean_object* v_positions_4616_, lean_object* v_motives_4617_, lean_object* v_isIndPred_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
uint8_t v_isIndPred_boxed_4624_; lean_object* v_res_4625_; 
v_isIndPred_boxed_4624_ = lean_unbox(v_isIndPred_4618_);
v_res_4625_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4615_, v_positions_4616_, v_motives_4617_, v_isIndPred_boxed_4624_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec_ref(v_motives_4617_);
lean_dec_ref(v_positions_4616_);
lean_dec_ref(v_recArgInfos_4615_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4626_, lean_object* v_msg_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4634_, lean_object* v_msg_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4634_, v_msg_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4642_, lean_object* v_00_u03b1_4643_, lean_object* v_f_4644_, lean_object* v_positions_4645_, lean_object* v_ys_4646_, lean_object* v_xs_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4644_, v_positions_4645_, v_ys_4646_, v_xs_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4654_, lean_object* v_00_u03b1_4655_, lean_object* v_f_4656_, lean_object* v_positions_4657_, lean_object* v_ys_4658_, lean_object* v_xs_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4654_, v_00_u03b1_4655_, v_f_4656_, v_positions_4657_, v_ys_4658_, v_xs_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec_ref(v_xs_4659_);
lean_dec_ref(v_ys_4658_);
lean_dec_ref(v_positions_4657_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4666_, lean_object* v_00_u03b3_4667_, lean_object* v_xs_4668_, lean_object* v_f_4669_, lean_object* v_as_4670_, lean_object* v_bs_4671_, lean_object* v_i_4672_, lean_object* v_cs_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v___x_4679_; 
v___x_4679_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4668_, v_f_4669_, v_as_4670_, v_bs_4671_, v_i_4672_, v_cs_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4680_, lean_object* v_00_u03b3_4681_, lean_object* v_xs_4682_, lean_object* v_f_4683_, lean_object* v_as_4684_, lean_object* v_bs_4685_, lean_object* v_i_4686_, lean_object* v_cs_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4680_, v_00_u03b3_4681_, v_xs_4682_, v_f_4683_, v_as_4684_, v_bs_4685_, v_i_4686_, v_cs_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec_ref(v_bs_4685_);
lean_dec_ref(v_as_4684_);
lean_dec_ref(v_xs_4682_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_4694_, lean_object* v_e_4695_){
_start:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; 
v___x_4696_ = l_Lean_indentD(v_e_4695_);
v___x_4697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4694_);
lean_ctor_set(v___x_4697_, 1, v___x_4696_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_4698_, lean_object* v_x_4699_, lean_object* v_brecOnType_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4698_, v_brecOnType_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_4707_, lean_object* v_x_4708_, lean_object* v_brecOnType_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_4707_, v_x_4708_, v_brecOnType_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec_ref(v_x_4708_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4716_, lean_object* v_as_4717_, size_t v_sz_4718_, size_t v_i_4719_, lean_object* v_b_4720_){
_start:
{
uint8_t v___x_4722_; 
v___x_4722_ = lean_usize_dec_lt(v_i_4719_, v_sz_4718_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; 
lean_dec_ref(v_a_4716_);
v___x_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4723_, 0, v_b_4720_);
return v___x_4723_;
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4725_; size_t v___x_4726_; size_t v___x_4727_; 
v_a_4724_ = lean_array_uget_borrowed(v_as_4717_, v_i_4719_);
lean_inc_ref(v_a_4716_);
v___x_4725_ = lean_array_set(v_b_4720_, v_a_4724_, v_a_4716_);
v___x_4726_ = ((size_t)1ULL);
v___x_4727_ = lean_usize_add(v_i_4719_, v___x_4726_);
v_i_4719_ = v___x_4727_;
v_b_4720_ = v___x_4725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4729_, lean_object* v_as_4730_, lean_object* v_sz_4731_, lean_object* v_i_4732_, lean_object* v_b_4733_, lean_object* v___y_4734_){
_start:
{
size_t v_sz_boxed_4735_; size_t v_i_boxed_4736_; lean_object* v_res_4737_; 
v_sz_boxed_4735_ = lean_unbox_usize(v_sz_4731_);
lean_dec(v_sz_4731_);
v_i_boxed_4736_ = lean_unbox_usize(v_i_4732_);
lean_dec(v_i_4732_);
v_res_4737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4729_, v_as_4730_, v_sz_boxed_4735_, v_i_boxed_4736_, v_b_4733_);
lean_dec_ref(v_as_4730_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4738_, size_t v_sz_4739_, size_t v_i_4740_, lean_object* v_b_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
uint8_t v___x_4747_; 
v___x_4747_ = lean_usize_dec_lt(v_i_4740_, v_sz_4739_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; 
v___x_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4748_, 0, v_b_4741_);
return v___x_4748_;
}
else
{
lean_object* v_snd_4749_; lean_object* v_fst_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4794_; 
v_snd_4749_ = lean_ctor_get(v_b_4741_, 1);
v_fst_4750_ = lean_ctor_get(v_b_4741_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v_b_4741_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4752_ = v_b_4741_;
v_isShared_4753_ = v_isSharedCheck_4794_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_snd_4749_);
lean_inc(v_fst_4750_);
lean_dec(v_b_4741_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4794_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v_array_4754_; lean_object* v_start_4755_; lean_object* v_stop_4756_; uint8_t v___x_4757_; 
v_array_4754_ = lean_ctor_get(v_snd_4749_, 0);
v_start_4755_ = lean_ctor_get(v_snd_4749_, 1);
v_stop_4756_ = lean_ctor_get(v_snd_4749_, 2);
v___x_4757_ = lean_nat_dec_lt(v_start_4755_, v_stop_4756_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4759_; 
if (v_isShared_4753_ == 0)
{
v___x_4759_ = v___x_4752_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_fst_4750_);
lean_ctor_set(v_reuseFailAlloc_4761_, 1, v_snd_4749_);
v___x_4759_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
lean_object* v___x_4760_; 
v___x_4760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4759_);
return v___x_4760_;
}
}
else
{
lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4790_; 
lean_inc(v_stop_4756_);
lean_inc(v_start_4755_);
lean_inc_ref(v_array_4754_);
v_isSharedCheck_4790_ = !lean_is_exclusive(v_snd_4749_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; lean_object* v_unused_4792_; lean_object* v_unused_4793_; 
v_unused_4791_ = lean_ctor_get(v_snd_4749_, 2);
lean_dec(v_unused_4791_);
v_unused_4792_ = lean_ctor_get(v_snd_4749_, 1);
lean_dec(v_unused_4792_);
v_unused_4793_ = lean_ctor_get(v_snd_4749_, 0);
lean_dec(v_unused_4793_);
v___x_4763_ = v_snd_4749_;
v_isShared_4764_ = v_isSharedCheck_4790_;
goto v_resetjp_4762_;
}
else
{
lean_dec(v_snd_4749_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4790_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v_a_4765_; lean_object* v___x_4766_; size_t v_sz_4767_; size_t v___x_4768_; lean_object* v___x_4769_; 
v_a_4765_ = lean_array_uget_borrowed(v_as_4738_, v_i_4740_);
v___x_4766_ = lean_array_fget_borrowed(v_array_4754_, v_start_4755_);
v_sz_4767_ = lean_array_size(v___x_4766_);
v___x_4768_ = ((size_t)0ULL);
lean_inc(v_a_4765_);
v___x_4769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4765_, v___x_4766_, v_sz_4767_, v___x_4768_, v_fst_4750_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4770_);
lean_dec_ref_known(v___x_4769_, 1);
v___x_4771_ = lean_unsigned_to_nat(1u);
v___x_4772_ = lean_nat_add(v_start_4755_, v___x_4771_);
lean_dec(v_start_4755_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 1, v___x_4772_);
v___x_4774_ = v___x_4763_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_array_4754_);
lean_ctor_set(v_reuseFailAlloc_4781_, 1, v___x_4772_);
lean_ctor_set(v_reuseFailAlloc_4781_, 2, v_stop_4756_);
v___x_4774_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
lean_object* v___x_4776_; 
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 1, v___x_4774_);
lean_ctor_set(v___x_4752_, 0, v_a_4770_);
v___x_4776_ = v___x_4752_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4770_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v___x_4774_);
v___x_4776_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
size_t v___x_4777_; size_t v___x_4778_; 
v___x_4777_ = ((size_t)1ULL);
v___x_4778_ = lean_usize_add(v_i_4740_, v___x_4777_);
v_i_4740_ = v___x_4778_;
v_b_4741_ = v___x_4776_;
goto _start;
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_del_object(v___x_4763_);
lean_dec(v_stop_4756_);
lean_dec(v_start_4755_);
lean_dec_ref(v_array_4754_);
lean_del_object(v___x_4752_);
v_a_4782_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4769_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4769_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4795_, lean_object* v_sz_4796_, lean_object* v_i_4797_, lean_object* v_b_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_){
_start:
{
size_t v_sz_boxed_4804_; size_t v_i_boxed_4805_; lean_object* v_res_4806_; 
v_sz_boxed_4804_ = lean_unbox_usize(v_sz_4796_);
lean_dec(v_sz_4796_);
v_i_boxed_4805_ = lean_unbox_usize(v_i_4797_);
lean_dec(v_i_4797_);
v_res_4806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4795_, v_sz_boxed_4804_, v_i_boxed_4805_, v_b_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec(v___y_4800_);
lean_dec_ref(v___y_4799_);
lean_dec_ref(v_as_4795_);
return v_res_4806_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4809_ = l_Lean_stringToMessageData(v___x_4808_);
return v___x_4809_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___f_4811_; 
v___x_4810_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4811_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_4811_, 0, v___x_4810_);
return v___f_4811_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4813_ = l_Lean_Expr_sort___override(v___x_4812_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4814_, lean_object* v_positions_4815_, lean_object* v_brecOnConst_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_){
_start:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v_recArgInfo_4824_; lean_object* v_indicesPos_4825_; lean_object* v_indIdx_4826_; lean_object* v_brecOn_4827_; lean_object* v___f_4828_; uint8_t v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4822_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4823_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4824_ = lean_array_get_borrowed(v___x_4822_, v_recArgInfos_4814_, v___x_4823_);
v_indicesPos_4825_ = lean_ctor_get(v_recArgInfo_4824_, 3);
v_indIdx_4826_ = lean_ctor_get(v_recArgInfo_4824_, 5);
lean_inc(v_indIdx_4826_);
v_brecOn_4827_ = lean_apply_1(v_brecOnConst_4816_, v_indIdx_4826_);
v___f_4828_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4829_ = 0;
v___x_4830_ = lean_box(v___x_4829_);
lean_inc_ref(v_brecOn_4827_);
v___x_4831_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4831_, 0, v_brecOn_4827_);
lean_closure_set(v___x_4831_, 1, v___x_4830_);
v___x_4832_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4831_, v___f_4828_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v___x_4833_; 
lean_dec_ref_known(v___x_4832_, 1);
lean_inc(v_a_4820_);
lean_inc_ref(v_a_4819_);
lean_inc(v_a_4818_);
lean_inc_ref(v_a_4817_);
v___x_4833_ = lean_infer_type(v_brecOn_4827_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v_numTypeFormers_4835_; lean_object* v___f_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; uint8_t v___x_4841_; lean_object* v___x_4842_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
lean_inc(v_a_4834_);
lean_dec_ref_known(v___x_4833_, 1);
v_numTypeFormers_4835_ = lean_array_get_size(v_positions_4815_);
v___f_4836_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4836_, 0, v_numTypeFormers_4835_);
v___x_4837_ = lean_array_get_size(v_indicesPos_4825_);
v___x_4838_ = lean_unsigned_to_nat(1u);
v___x_4839_ = lean_nat_add(v___x_4837_, v___x_4838_);
v___x_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
v___x_4841_ = 0;
v___x_4842_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4834_, v___x_4840_, v___f_4836_, v___x_4841_, v___x_4841_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; size_t v_sz_4849_; size_t v___x_4850_; lean_object* v___x_4851_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref_known(v___x_4842_, 1);
v___x_4844_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4815_);
v___x_4845_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4846_ = lean_mk_array(v___x_4844_, v___x_4845_);
v___x_4847_ = l_Array_toSubarray___redArg(v_positions_4815_, v___x_4823_, v_numTypeFormers_4835_);
v___x_4848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4846_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
v_sz_4849_ = lean_array_size(v_a_4843_);
v___x_4850_ = ((size_t)0ULL);
v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4843_, v_sz_4849_, v___x_4850_, v___x_4848_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
lean_dec(v_a_4843_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4860_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_4860_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4860_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v_fst_4856_; lean_object* v___x_4858_; 
v_fst_4856_ = lean_ctor_get(v_a_4852_, 0);
lean_inc(v_fst_4856_);
lean_dec(v_a_4852_);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v_fst_4856_);
v___x_4858_ = v___x_4854_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_fst_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
v_a_4861_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4851_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4851_);
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
else
{
lean_dec_ref(v_positions_4815_);
return v___x_4842_;
}
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec_ref(v_positions_4815_);
v_a_4869_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4833_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4833_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec_ref(v_brecOn_4827_);
lean_dec_ref(v_positions_4815_);
v_a_4877_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4832_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4832_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4885_, lean_object* v_positions_4886_, lean_object* v_brecOnConst_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4885_, v_positions_4886_, v_brecOnConst_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4888_);
lean_dec_ref(v_recArgInfos_4885_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4894_, lean_object* v_as_4895_, size_t v_sz_4896_, size_t v_i_4897_, lean_object* v_b_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
lean_object* v___x_4904_; 
v___x_4904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4894_, v_as_4895_, v_sz_4896_, v_i_4897_, v_b_4898_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4905_, lean_object* v_as_4906_, lean_object* v_sz_4907_, lean_object* v_i_4908_, lean_object* v_b_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
size_t v_sz_boxed_4915_; size_t v_i_boxed_4916_; lean_object* v_res_4917_; 
v_sz_boxed_4915_ = lean_unbox_usize(v_sz_4907_);
lean_dec(v_sz_4907_);
v_i_boxed_4916_ = lean_unbox_usize(v_i_4908_);
lean_dec(v_i_4908_);
v_res_4917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4905_, v_as_4906_, v_sz_boxed_4915_, v_i_boxed_4916_, v_b_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec_ref(v_as_4906_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4918_, lean_object* v_a_4919_){
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
lean_object* v_head_4921_; lean_object* v_tail_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4933_; 
v_head_4921_ = lean_ctor_get(v_a_4918_, 0);
v_tail_4922_ = lean_ctor_get(v_a_4918_, 1);
v_isSharedCheck_4933_ = !lean_is_exclusive(v_a_4918_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4924_ = v_a_4918_;
v_isShared_4925_ = v_isSharedCheck_4933_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_tail_4922_);
lean_inc(v_head_4921_);
lean_dec(v_a_4918_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4933_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4930_; 
v___x_4926_ = l_Nat_reprFast(v_head_4921_);
v___x_4927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
v___x_4928_ = l_Lean_MessageData_ofFormat(v___x_4927_);
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 1, v_a_4919_);
lean_ctor_set(v___x_4924_, 0, v___x_4928_);
v___x_4930_ = v___x_4924_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v___x_4928_);
lean_ctor_set(v_reuseFailAlloc_4932_, 1, v_a_4919_);
v___x_4930_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
v_a_4918_ = v_tail_4922_;
v_a_4919_ = v___x_4930_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4934_, lean_object* v_a_4935_){
_start:
{
if (lean_obj_tag(v_a_4934_) == 0)
{
lean_object* v___x_4936_; 
v___x_4936_ = l_List_reverse___redArg(v_a_4935_);
return v___x_4936_;
}
else
{
lean_object* v_head_4937_; lean_object* v_tail_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4950_; 
v_head_4937_ = lean_ctor_get(v_a_4934_, 0);
v_tail_4938_ = lean_ctor_get(v_a_4934_, 1);
v_isSharedCheck_4950_ = !lean_is_exclusive(v_a_4934_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4940_ = v_a_4934_;
v_isShared_4941_ = v_isSharedCheck_4950_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_tail_4938_);
lean_inc(v_head_4937_);
lean_dec(v_a_4934_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4950_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4947_; 
v___x_4942_ = lean_array_to_list(v_head_4937_);
v___x_4943_ = lean_box(0);
v___x_4944_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4942_, v___x_4943_);
v___x_4945_ = l_Lean_MessageData_ofList(v___x_4944_);
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v_a_4935_);
lean_ctor_set(v___x_4940_, 0, v___x_4945_);
v___x_4947_ = v___x_4940_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4945_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_a_4935_);
v___x_4947_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
v_a_4934_ = v_tail_4938_;
v_a_4935_ = v___x_4947_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4951_, lean_object* v_v_4952_, lean_object* v_i_4953_){
_start:
{
lean_object* v___x_4954_; uint8_t v___x_4955_; 
v___x_4954_ = lean_array_get_size(v_xs_4951_);
v___x_4955_ = lean_nat_dec_lt(v_i_4953_, v___x_4954_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; 
lean_dec(v_i_4953_);
v___x_4956_ = lean_box(0);
return v___x_4956_;
}
else
{
lean_object* v___x_4957_; uint8_t v___x_4958_; 
v___x_4957_ = lean_array_fget_borrowed(v_xs_4951_, v_i_4953_);
v___x_4958_ = lean_nat_dec_eq(v___x_4957_, v_v_4952_);
if (v___x_4958_ == 0)
{
lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4959_ = lean_unsigned_to_nat(1u);
v___x_4960_ = lean_nat_add(v_i_4953_, v___x_4959_);
lean_dec(v_i_4953_);
v_i_4953_ = v___x_4960_;
goto _start;
}
else
{
lean_object* v___x_4962_; 
v___x_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4962_, 0, v_i_4953_);
return v___x_4962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4963_, lean_object* v_v_4964_, lean_object* v_i_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4963_, v_v_4964_, v_i_4965_);
lean_dec(v_v_4964_);
lean_dec_ref(v_xs_4963_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4967_, lean_object* v_v_4968_){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4969_ = lean_unsigned_to_nat(0u);
v___x_4970_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4967_, v_v_4968_, v___x_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4971_, lean_object* v_v_4972_){
_start:
{
lean_object* v_res_4973_; 
v_res_4973_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4971_, v_v_4972_);
lean_dec(v_v_4972_);
lean_dec_ref(v_xs_4971_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4977_, lean_object* v_as_4978_, size_t v_sz_4979_, size_t v_i_4980_, lean_object* v_b_4981_){
_start:
{
uint8_t v___x_4982_; 
v___x_4982_ = lean_usize_dec_lt(v_i_4980_, v_sz_4979_);
if (v___x_4982_ == 0)
{
lean_inc_ref(v_b_4981_);
return v_b_4981_;
}
else
{
lean_object* v___x_4983_; lean_object* v_a_4984_; lean_object* v___x_4985_; 
v___x_4983_ = lean_box(0);
v_a_4984_ = lean_array_uget_borrowed(v_as_4978_, v_i_4980_);
v___x_4985_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4984_, v_fnIdx_4977_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v___x_4986_; size_t v___x_4987_; size_t v___x_4988_; 
v___x_4986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4987_ = ((size_t)1ULL);
v___x_4988_ = lean_usize_add(v_i_4980_, v___x_4987_);
v_i_4980_ = v___x_4988_;
v_b_4981_ = v___x_4986_;
goto _start;
}
else
{
lean_object* v_val_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_5001_; 
v_val_4990_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4992_ = v___x_4985_;
v_isShared_4993_ = v_isSharedCheck_5001_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_val_4990_);
lean_dec(v___x_4985_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_5001_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4997_; 
v___x_4994_ = lean_array_get_size(v_a_4984_);
v___x_4995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
lean_ctor_set(v___x_4995_, 1, v_val_4990_);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v___x_4995_);
v___x_4997_ = v___x_4992_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v___x_4995_);
v___x_4997_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4997_);
v___x_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4998_);
lean_ctor_set(v___x_4999_, 1, v___x_4983_);
return v___x_4999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_5002_, lean_object* v_as_5003_, lean_object* v_sz_5004_, lean_object* v_i_5005_, lean_object* v_b_5006_){
_start:
{
size_t v_sz_boxed_5007_; size_t v_i_boxed_5008_; lean_object* v_res_5009_; 
v_sz_boxed_5007_ = lean_unbox_usize(v_sz_5004_);
lean_dec(v_sz_5004_);
v_i_boxed_5008_ = lean_unbox_usize(v_i_5005_);
lean_dec(v_i_5005_);
v_res_5009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5002_, v_as_5003_, v_sz_boxed_5007_, v_i_boxed_5008_, v_b_5006_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_as_5003_);
lean_dec(v_fnIdx_5002_);
return v_res_5009_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_5012_ = l_Lean_stringToMessageData(v___x_5011_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_5013_, lean_object* v_positions_5014_, lean_object* v_fnIdx_5015_, lean_object* v_brecOnConst_5016_, lean_object* v_packedFArgs_5017_, lean_object* v_funTypes_5018_, lean_object* v_ys_5019_, lean_object* v___value_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v___y_5027_; lean_object* v___y_5028_; lean_object* v___y_5029_; lean_object* v___y_5030_; lean_object* v___x_5044_; lean_object* v_fst_5045_; lean_object* v_snd_5046_; lean_object* v___x_5047_; size_t v_sz_5048_; size_t v___x_5049_; lean_object* v___x_5050_; lean_object* v_fst_5051_; 
lean_inc_ref(v_ys_5019_);
lean_inc_ref(v_recArgInfo_5013_);
v___x_5044_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_5013_, v_ys_5019_);
v_fst_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_fst_5045_);
v_snd_5046_ = lean_ctor_get(v___x_5044_, 1);
lean_inc(v_snd_5046_);
lean_dec_ref(v___x_5044_);
v___x_5047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5048_ = lean_array_size(v_positions_5014_);
v___x_5049_ = ((size_t)0ULL);
v___x_5050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5015_, v_positions_5014_, v_sz_5048_, v___x_5049_, v___x_5047_);
v_fst_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_fst_5051_);
lean_dec_ref(v___x_5050_);
if (lean_obj_tag(v_fst_5051_) == 0)
{
lean_dec(v_snd_5046_);
lean_dec(v_fst_5045_);
lean_dec_ref(v_ys_5019_);
lean_dec_ref(v_brecOnConst_5016_);
lean_dec_ref(v_recArgInfo_5013_);
v___y_5027_ = v___y_5021_;
v___y_5028_ = v___y_5022_;
v___y_5029_ = v___y_5023_;
v___y_5030_ = v___y_5024_;
goto v___jp_5026_;
}
else
{
lean_object* v_val_5052_; 
v_val_5052_ = lean_ctor_get(v_fst_5051_, 0);
lean_inc(v_val_5052_);
lean_dec_ref_known(v_fst_5051_, 1);
if (lean_obj_tag(v_val_5052_) == 1)
{
lean_object* v_val_5053_; lean_object* v_fst_5054_; lean_object* v_snd_5055_; lean_object* v_indIdx_5056_; lean_object* v_brecOn_5057_; lean_object* v_brecOn_5058_; lean_object* v_brecOn_5059_; lean_object* v___x_5060_; 
lean_dec(v_fnIdx_5015_);
lean_dec_ref(v_positions_5014_);
v_val_5053_ = lean_ctor_get(v_val_5052_, 0);
lean_inc(v_val_5053_);
lean_dec_ref_known(v_val_5052_, 1);
v_fst_5054_ = lean_ctor_get(v_val_5053_, 0);
lean_inc(v_fst_5054_);
v_snd_5055_ = lean_ctor_get(v_val_5053_, 1);
lean_inc(v_snd_5055_);
lean_dec(v_val_5053_);
v_indIdx_5056_ = lean_ctor_get(v_recArgInfo_5013_, 5);
lean_inc(v_indIdx_5056_);
lean_dec_ref(v_recArgInfo_5013_);
v_brecOn_5057_ = lean_apply_1(v_brecOnConst_5016_, v_indIdx_5056_);
v_brecOn_5058_ = l_Lean_mkAppN(v_brecOn_5057_, v_fst_5045_);
lean_dec(v_fst_5045_);
v_brecOn_5059_ = l_Lean_mkAppN(v_brecOn_5058_, v_packedFArgs_5017_);
v___x_5060_ = l_Lean_Meta_PProdN_projM(v_fst_5054_, v_snd_5055_, v_brecOn_5059_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec(v_snd_5055_);
lean_dec(v_fst_5054_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5062_; uint8_t v___x_5063_; uint8_t v___x_5064_; lean_object* v___x_5065_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v___x_5062_ = l_Lean_mkAppN(v_a_5061_, v_snd_5046_);
lean_dec(v_snd_5046_);
v___x_5063_ = 1;
v___x_5064_ = 1;
v___x_5065_ = l_Lean_Meta_mkLetFVars(v_funTypes_5018_, v___x_5062_, v___x_5063_, v___x_5063_, v___x_5064_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; uint8_t v___x_5067_; lean_object* v___x_5068_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v___x_5065_, 1);
v___x_5067_ = 0;
v___x_5068_ = l_Lean_Meta_mkLambdaFVars(v_ys_5019_, v_a_5066_, v___x_5067_, v___x_5063_, v___x_5067_, v___x_5063_, v___x_5064_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec_ref(v_ys_5019_);
return v___x_5068_;
}
else
{
lean_dec_ref(v_ys_5019_);
return v___x_5065_;
}
}
else
{
lean_dec(v_snd_5046_);
lean_dec_ref(v_ys_5019_);
return v___x_5060_;
}
}
else
{
lean_dec(v_val_5052_);
lean_dec(v_snd_5046_);
lean_dec(v_fst_5045_);
lean_dec_ref(v_ys_5019_);
lean_dec_ref(v_brecOnConst_5016_);
lean_dec_ref(v_recArgInfo_5013_);
v___y_5027_ = v___y_5021_;
v___y_5028_ = v___y_5022_;
v___y_5029_ = v___y_5023_;
v___y_5030_ = v___y_5024_;
goto v___jp_5026_;
}
}
v___jp_5026_:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5031_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_5032_ = l_Nat_reprFast(v_fnIdx_5015_);
v___x_5033_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5032_);
v___x_5034_ = l_Lean_MessageData_ofFormat(v___x_5033_);
v___x_5035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5031_);
lean_ctor_set(v___x_5035_, 1, v___x_5034_);
v___x_5036_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_5037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5035_);
lean_ctor_set(v___x_5037_, 1, v___x_5036_);
v___x_5038_ = lean_array_to_list(v_positions_5014_);
v___x_5039_ = lean_box(0);
v___x_5040_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5038_, v___x_5039_);
v___x_5041_ = l_Lean_MessageData_ofList(v___x_5040_);
v___x_5042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5037_);
lean_ctor_set(v___x_5042_, 1, v___x_5041_);
v___x_5043_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5042_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
return v___x_5043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5069_, lean_object* v_positions_5070_, lean_object* v_fnIdx_5071_, lean_object* v_brecOnConst_5072_, lean_object* v_packedFArgs_5073_, lean_object* v_funTypes_5074_, lean_object* v_ys_5075_, lean_object* v___value_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5069_, v_positions_5070_, v_fnIdx_5071_, v_brecOnConst_5072_, v_packedFArgs_5073_, v_funTypes_5074_, v_ys_5075_, v___value_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec_ref(v___value_5076_);
lean_dec_ref(v_funTypes_5074_);
lean_dec_ref(v_packedFArgs_5073_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5083_, lean_object* v_fnIdx_5084_, lean_object* v_brecOnConst_5085_, lean_object* v_packedFArgs_5086_, lean_object* v_funTypes_5087_, lean_object* v_recArgInfo_5088_, lean_object* v_value_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_){
_start:
{
lean_object* v___f_5095_; uint8_t v___x_5096_; lean_object* v___x_5097_; 
v___f_5095_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5095_, 0, v_recArgInfo_5088_);
lean_closure_set(v___f_5095_, 1, v_positions_5083_);
lean_closure_set(v___f_5095_, 2, v_fnIdx_5084_);
lean_closure_set(v___f_5095_, 3, v_brecOnConst_5085_);
lean_closure_set(v___f_5095_, 4, v_packedFArgs_5086_);
lean_closure_set(v___f_5095_, 5, v_funTypes_5087_);
v___x_5096_ = 0;
v___x_5097_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5089_, v___f_5095_, v___x_5096_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5098_, lean_object* v_fnIdx_5099_, lean_object* v_brecOnConst_5100_, lean_object* v_packedFArgs_5101_, lean_object* v_funTypes_5102_, lean_object* v_recArgInfo_5103_, lean_object* v_value_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5098_, v_fnIdx_5099_, v_brecOnConst_5100_, v_packedFArgs_5101_, v_funTypes_5102_, v_recArgInfo_5103_, v_value_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_);
lean_dec(v_a_5108_);
lean_dec_ref(v_a_5107_);
lean_dec(v_a_5106_);
lean_dec_ref(v_a_5105_);
return v_res_5110_;
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
