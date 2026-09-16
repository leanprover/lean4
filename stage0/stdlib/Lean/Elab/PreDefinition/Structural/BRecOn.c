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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_packLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_projM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_PProdN_packLambdas___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not type correct!"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "initial belowDict for "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7;
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
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object*, lean_object*);
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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
lean_inc(v_ref_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_ref_30_);
lean_ctor_set(v___x_36_, 1, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__0));
v___x_50_ = l_Lean_stringToMessageData(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1);
v___x_57_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_56_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___boxed(lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_58_, v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(lean_object* v_00_u03b1_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_65_, v_a_66_, v_a_67_, v_a_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___boxed(lean_object* v_00_u03b1_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(v_00_u03b1_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(lean_object* v_00_u03b1_78_, lean_object* v_msg_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___boxed(lean_object* v_00_u03b1_86_, lean_object* v_msg_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(v_00_u03b1_86_, v_msg_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg(lean_object* v_e_102_, lean_object* v_F_103_, lean_object* v_k_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; 
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
lean_inc_ref(v_e_102_);
v___x_110_ = lean_whnf(v_e_102_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_110_, 1);
switch(lean_obj_tag(v_a_111_))
{
case 5:
{
lean_object* v_fn_112_; 
v_fn_112_ = lean_ctor_get(v_a_111_, 0);
lean_inc_ref(v_fn_112_);
if (lean_obj_tag(v_fn_112_) == 5)
{
lean_object* v_fn_113_; 
v_fn_113_ = lean_ctor_get(v_fn_112_, 0);
if (lean_obj_tag(v_fn_113_) == 4)
{
lean_object* v_declName_114_; 
v_declName_114_ = lean_ctor_get(v_fn_113_, 0);
lean_inc(v_declName_114_);
if (lean_obj_tag(v_declName_114_) == 1)
{
lean_object* v_pre_115_; 
v_pre_115_ = lean_ctor_get(v_declName_114_, 0);
if (lean_obj_tag(v_pre_115_) == 0)
{
lean_object* v_arg_116_; lean_object* v_arg_117_; lean_object* v_str_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_arg_116_ = lean_ctor_get(v_a_111_, 1);
lean_inc_ref(v_arg_116_);
lean_dec_ref_known(v_a_111_, 2);
v_arg_117_ = lean_ctor_get(v_fn_112_, 1);
lean_inc_ref(v_arg_117_);
lean_dec_ref_known(v_fn_112_, 2);
v_str_118_ = lean_ctor_get(v_declName_114_, 1);
lean_inc_ref(v_str_118_);
lean_dec_ref_known(v_declName_114_, 2);
v___x_119_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__0));
v___x_120_ = lean_string_dec_eq(v_str_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__1));
v___x_122_ = lean_string_dec_eq(v_str_118_, v___x_121_);
lean_dec_ref(v_str_118_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_116_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_123_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec_ref(v_e_102_);
v___x_124_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__2));
v___x_125_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_103_);
v___x_126_ = l_Lean_Expr_proj___override(v___x_124_, v___x_125_, v_F_103_);
v___x_127_ = l_Lean_Meta_saveState___redArg(v_a_106_, v_a_108_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; lean_object* v___x_129_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_127_, 1);
lean_inc_ref(v_k_104_);
v___x_129_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_117_, v___x_126_, v_k_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_dec(v_a_128_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
return v___x_129_;
}
else
{
lean_object* v_a_130_; uint8_t v___y_132_; uint8_t v___x_145_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
v___x_145_ = l_Lean_Exception_isInterrupt(v_a_130_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; 
v___x_146_ = l_Lean_Exception_isRuntime(v_a_130_);
v___y_132_ = v___x_146_;
goto v___jp_131_;
}
else
{
lean_dec(v_a_130_);
v___y_132_ = v___x_145_;
goto v___jp_131_;
}
v___jp_131_:
{
if (v___y_132_ == 0)
{
lean_object* v___x_133_; 
lean_dec_ref_known(v___x_129_, 1);
v___x_133_ = l_Lean_Meta_SavedState_restore___redArg(v_a_128_, v_a_106_, v_a_108_);
lean_dec(v_a_128_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec_ref_known(v___x_133_, 1);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = l_Lean_Expr_proj___override(v___x_124_, v___x_134_, v_F_103_);
v_e_102_ = v_arg_116_;
v_F_103_ = v___x_135_;
goto _start;
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
v_a_137_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_133_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_133_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_dec(v_a_128_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v___x_126_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
v_a_147_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_127_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_127_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec_ref(v_str_118_);
lean_dec_ref(v_e_102_);
v___x_155_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__3));
v___x_156_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_103_);
v___x_157_ = l_Lean_Expr_proj___override(v___x_155_, v___x_156_, v_F_103_);
v___x_158_ = l_Lean_Meta_saveState___redArg(v_a_106_, v_a_108_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
lean_inc_ref(v_k_104_);
v___x_160_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_117_, v___x_157_, v_k_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_dec(v_a_159_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
return v___x_160_;
}
else
{
lean_object* v_a_161_; uint8_t v___y_163_; uint8_t v___x_176_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
v___x_176_ = l_Lean_Exception_isInterrupt(v_a_161_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
v___x_177_ = l_Lean_Exception_isRuntime(v_a_161_);
v___y_163_ = v___x_177_;
goto v___jp_162_;
}
else
{
lean_dec(v_a_161_);
v___y_163_ = v___x_176_;
goto v___jp_162_;
}
v___jp_162_:
{
if (v___y_163_ == 0)
{
lean_object* v___x_164_; 
lean_dec_ref_known(v___x_160_, 1);
v___x_164_ = l_Lean_Meta_SavedState_restore___redArg(v_a_159_, v_a_106_, v_a_108_);
lean_dec(v_a_159_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref_known(v___x_164_, 1);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = l_Lean_Expr_proj___override(v___x_155_, v___x_165_, v_F_103_);
v_e_102_ = v_arg_116_;
v_F_103_ = v___x_166_;
goto _start;
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
v_a_168_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_164_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_164_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_dec(v_a_159_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
return v___x_160_;
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v___x_157_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
v_a_178_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_158_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_158_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
else
{
lean_object* v___x_186_; 
lean_dec_ref_known(v_declName_114_, 2);
lean_dec_ref_known(v_fn_112_, 2);
lean_dec_ref_known(v_a_111_, 2);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_186_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_186_;
}
}
else
{
lean_object* v___x_187_; 
lean_dec(v_declName_114_);
lean_dec_ref_known(v_fn_112_, 2);
lean_dec_ref_known(v_a_111_, 2);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_187_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_187_;
}
}
else
{
lean_object* v___x_188_; 
lean_dec_ref_known(v_fn_112_, 2);
lean_dec_ref_known(v_a_111_, 2);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_188_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_188_;
}
}
else
{
lean_object* v___x_189_; 
lean_dec_ref(v_fn_112_);
lean_dec_ref_known(v_a_111_, 2);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_189_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_189_;
}
}
case 4:
{
lean_object* v_declName_190_; 
v_declName_190_ = lean_ctor_get(v_a_111_, 0);
lean_inc(v_declName_190_);
lean_dec_ref_known(v_a_111_, 2);
if (lean_obj_tag(v_declName_190_) == 1)
{
lean_object* v_pre_191_; 
v_pre_191_ = lean_ctor_get(v_declName_190_, 0);
if (lean_obj_tag(v_pre_191_) == 0)
{
lean_object* v_str_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_str_192_ = lean_ctor_get(v_declName_190_, 1);
lean_inc_ref(v_str_192_);
lean_dec_ref_known(v_declName_190_, 2);
v___x_193_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__4));
v___x_194_ = lean_string_dec_eq(v_str_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__5));
v___x_196_ = lean_string_dec_eq(v_str_192_, v___x_195_);
lean_dec_ref(v_str_192_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_197_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_197_;
}
else
{
lean_object* v___x_198_; 
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
lean_dec_ref(v_e_102_);
v___x_198_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_105_, v_a_106_, v_a_107_, v_a_108_);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec_ref(v_str_192_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
lean_dec_ref(v_e_102_);
v___x_199_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_105_, v_a_106_, v_a_107_, v_a_108_);
return v___x_199_;
}
}
else
{
lean_object* v___x_200_; 
lean_dec_ref_known(v_declName_190_, 2);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_200_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_200_;
}
}
else
{
lean_object* v___x_201_; 
lean_dec(v_declName_190_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_201_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_201_;
}
}
default: 
{
lean_object* v___x_202_; 
lean_dec(v_a_111_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v___x_202_ = lean_apply_7(v_k_104_, v_e_102_, v_F_103_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, lean_box(0));
return v___x_202_;
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
lean_dec_ref(v_e_102_);
v_a_203_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_110_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_110_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg___boxed(lean_object* v_e_211_, lean_object* v_F_212_, lean_object* v_k_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_211_, v_F_212_, v_k_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd(lean_object* v_00_u03b1_220_, lean_object* v_e_221_, lean_object* v_F_222_, lean_object* v_k_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_221_, v_F_222_, v_k_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___boxed(lean_object* v_00_u03b1_230_, lean_object* v_e_231_, lean_object* v_F_232_, lean_object* v_k_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Elab_Structural_searchPProd(v_00_u03b1_230_, v_e_231_, v_F_232_, v_k_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(lean_object* v_k_240_, lean_object* v_b_241_, lean_object* v_c_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; 
lean_inc(v___y_246_);
lean_inc_ref(v___y_245_);
lean_inc(v___y_244_);
lean_inc_ref(v___y_243_);
v___x_248_ = lean_apply_7(v_k_240_, v_b_241_, v_c_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, lean_box(0));
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_249_, lean_object* v_b_250_, lean_object* v_c_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(v_k_249_, v_b_250_, v_c_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(lean_object* v_type_258_, lean_object* v_k_259_, uint8_t v_cleanupAnnotations_260_, uint8_t v_whnfType_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___f_267_; lean_object* v___x_268_; 
v___f_267_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_267_, 0, v_k_259_);
v___x_268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_258_, v___f_267_, v_cleanupAnnotations_260_, v_whnfType_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_268_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_268_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___boxed(lean_object* v_type_285_, lean_object* v_k_286_, lean_object* v_cleanupAnnotations_287_, lean_object* v_whnfType_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_294_; uint8_t v_whnfType_boxed_295_; lean_object* v_res_296_; 
v_cleanupAnnotations_boxed_294_ = lean_unbox(v_cleanupAnnotations_287_);
v_whnfType_boxed_295_ = lean_unbox(v_whnfType_288_);
v_res_296_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_285_, v_k_286_, v_cleanupAnnotations_boxed_294_, v_whnfType_boxed_295_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_object* v_00_u03b1_297_, lean_object* v_type_298_, lean_object* v_k_299_, uint8_t v_cleanupAnnotations_300_, uint8_t v_whnfType_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_298_, v_k_299_, v_cleanupAnnotations_300_, v_whnfType_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___boxed(lean_object* v_00_u03b1_308_, lean_object* v_type_309_, lean_object* v_k_310_, lean_object* v_cleanupAnnotations_311_, lean_object* v_whnfType_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_318_; uint8_t v_whnfType_boxed_319_; lean_object* v_res_320_; 
v_cleanupAnnotations_boxed_318_ = lean_unbox(v_cleanupAnnotations_311_);
v_whnfType_boxed_319_ = lean_unbox(v_whnfType_312_);
v_res_320_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_00_u03b1_308_, v_type_309_, v_k_310_, v_cleanupAnnotations_boxed_318_, v_whnfType_boxed_319_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(lean_object* v_cls_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_toCold_330_; lean_object* v_options_331_; uint8_t v_hasTrace_332_; 
v_toCold_330_ = lean_ctor_get(v___y_327_, 0);
v_options_331_ = lean_ctor_get(v_toCold_330_, 2);
v_hasTrace_332_ = lean_ctor_get_uint8(v_options_331_, sizeof(void*)*1);
if (v_hasTrace_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_cls_324_);
v___x_333_ = lean_box(v_hasTrace_332_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
else
{
lean_object* v_inheritedTraceOptions_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_inheritedTraceOptions_335_ = lean_ctor_get(v_toCold_330_, 11);
v___x_336_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_337_ = l_Lean_Name_append(v___x_336_, v_cls_324_);
v___x_338_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_335_, v_options_331_, v___x_337_);
lean_dec(v___x_337_);
v___x_339_ = lean_box(v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed(lean_object* v_cls_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_347_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0(void){
_start:
{
lean_object* v___x_348_; double v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_float_of_nat(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(lean_object* v_cls_353_, lean_object* v_msg_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_ref_360_; lean_object* v___x_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_406_; 
v_ref_360_ = lean_ctor_get(v___y_357_, 2);
v___x_361_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_406_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_406_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_406_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v_traceState_367_; lean_object* v_env_368_; lean_object* v_nextMacroScope_369_; lean_object* v_ngen_370_; lean_object* v_auxDeclNGen_371_; lean_object* v_cache_372_; lean_object* v_messages_373_; lean_object* v_infoState_374_; lean_object* v_snapshotTasks_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_405_; 
v___x_366_ = lean_st_ref_take(v___y_358_);
v_traceState_367_ = lean_ctor_get(v___x_366_, 4);
v_env_368_ = lean_ctor_get(v___x_366_, 0);
v_nextMacroScope_369_ = lean_ctor_get(v___x_366_, 1);
v_ngen_370_ = lean_ctor_get(v___x_366_, 2);
v_auxDeclNGen_371_ = lean_ctor_get(v___x_366_, 3);
v_cache_372_ = lean_ctor_get(v___x_366_, 5);
v_messages_373_ = lean_ctor_get(v___x_366_, 6);
v_infoState_374_ = lean_ctor_get(v___x_366_, 7);
v_snapshotTasks_375_ = lean_ctor_get(v___x_366_, 8);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_405_ == 0)
{
v___x_377_ = v___x_366_;
v_isShared_378_ = v_isSharedCheck_405_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_snapshotTasks_375_);
lean_inc(v_infoState_374_);
lean_inc(v_messages_373_);
lean_inc(v_cache_372_);
lean_inc(v_traceState_367_);
lean_inc(v_auxDeclNGen_371_);
lean_inc(v_ngen_370_);
lean_inc(v_nextMacroScope_369_);
lean_inc(v_env_368_);
lean_dec(v___x_366_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_405_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
uint64_t v_tid_379_; lean_object* v_traces_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_404_; 
v_tid_379_ = lean_ctor_get_uint64(v_traceState_367_, sizeof(void*)*1);
v_traces_380_ = lean_ctor_get(v_traceState_367_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_traceState_367_);
if (v_isSharedCheck_404_ == 0)
{
v___x_382_ = v_traceState_367_;
v_isShared_383_ = v_isSharedCheck_404_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_traces_380_);
lean_dec(v_traceState_367_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_404_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; double v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_384_ = lean_box(0);
v___x_385_ = lean_box(0);
v___x_386_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_387_ = 0;
v___x_388_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_389_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_389_, 0, v_cls_353_);
lean_ctor_set(v___x_389_, 1, v___x_385_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
lean_ctor_set_float(v___x_389_, sizeof(void*)*3, v___x_386_);
lean_ctor_set_float(v___x_389_, sizeof(void*)*3 + 8, v___x_386_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3 + 16, v___x_387_);
v___x_390_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_391_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v_a_362_);
lean_ctor_set(v___x_391_, 2, v___x_390_);
lean_inc(v_ref_360_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_ref_360_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = l_Lean_PersistentArray_push___redArg(v_traces_380_, v___x_392_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_393_);
v___x_395_ = v___x_382_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_393_);
lean_ctor_set_uint64(v_reuseFailAlloc_403_, sizeof(void*)*1, v_tid_379_);
v___x_395_ = v_reuseFailAlloc_403_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 4, v___x_395_);
v___x_397_ = v___x_377_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_env_368_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_nextMacroScope_369_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_ngen_370_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_auxDeclNGen_371_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_402_, 5, v_cache_372_);
lean_ctor_set(v_reuseFailAlloc_402_, 6, v_messages_373_);
lean_ctor_set(v_reuseFailAlloc_402_, 7, v_infoState_374_);
lean_ctor_set(v_reuseFailAlloc_402_, 8, v_snapshotTasks_375_);
v___x_397_ = v_reuseFailAlloc_402_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = lean_st_ref_put(v___y_358_, v___x_397_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_384_);
v___x_400_ = v___x_364_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_384_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object* v_cls_407_, lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_407_, v_msg_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2));
v___x_420_ = l_Lean_stringToMessageData(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v_a_421_, lean_object* v_C_422_, lean_object* v_cls_423_, lean_object* v___f_424_, lean_object* v_belowDict_425_, lean_object* v_F_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___x_501_; 
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
v___x_501_ = lean_apply_5(v___f_424_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, lean_box(0));
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; uint8_t v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = lean_unbox(v_a_502_);
lean_dec(v_a_502_);
if (v___x_503_ == 0)
{
goto v___jp_465_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_425_);
v___x_505_ = l_Lean_indentExpr(v_belowDict_425_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_inc(v_cls_423_);
v___x_507_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_423_, v___x_506_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_dec_ref_known(v___x_507_, 1);
goto v___jp_465_;
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_F_426_);
lean_dec_ref(v_belowDict_425_);
lean_dec(v_cls_423_);
lean_dec_ref(v_a_421_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v_F_426_);
lean_dec_ref(v_belowDict_425_);
lean_dec(v_cls_423_);
lean_dec_ref(v_a_421_);
v_a_516_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_501_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_501_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
v___jp_432_:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_isExprDefEq(v___y_433_, v_a_421_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_456_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_456_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_456_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_456_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v___x_443_; 
v___x_443_ = lean_unbox(v_a_439_);
lean_dec(v_a_439_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_del_object(v___x_441_);
lean_dec_ref(v_F_426_);
v___x_444_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_434_, v___y_435_, v___y_436_, v___y_437_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
lean_object* v___x_454_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v_F_426_);
v___x_454_ = v___x_441_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_F_426_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_F_426_);
v_a_457_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_438_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_438_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
v___jp_465_:
{
if (lean_obj_tag(v_belowDict_425_) == 5)
{
lean_object* v_fn_466_; lean_object* v_arg_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
lean_dec(v_cls_423_);
v_fn_466_ = lean_ctor_get(v_belowDict_425_, 0);
lean_inc_ref(v_fn_466_);
v_arg_467_ = lean_ctor_get(v_belowDict_425_, 1);
lean_inc_ref(v_arg_467_);
lean_dec_ref_known(v_belowDict_425_, 2);
v___x_468_ = l_Lean_Expr_getAppFn(v_fn_466_);
lean_dec_ref(v_fn_466_);
v___x_469_ = lean_expr_eqv(v___x_468_, v_C_422_);
lean_dec_ref(v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_arg_467_);
lean_dec_ref(v_F_426_);
lean_dec_ref(v_a_421_);
v___x_470_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_427_, v___y_428_, v___y_429_, v___y_430_);
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
v___y_433_ = v_arg_467_;
v___y_434_ = v___y_427_;
v___y_435_ = v___y_428_;
v___y_436_ = v___y_429_;
v___y_437_ = v___y_430_;
goto v___jp_432_;
}
}
else
{
lean_object* v_toCold_479_; lean_object* v_options_480_; uint8_t v_hasTrace_481_; 
lean_dec_ref(v_F_426_);
lean_dec_ref(v_a_421_);
v_toCold_479_ = lean_ctor_get(v___y_429_, 0);
v_options_480_ = lean_ctor_get(v_toCold_479_, 2);
v_hasTrace_481_ = lean_ctor_get_uint8(v_options_480_, sizeof(void*)*1);
if (v_hasTrace_481_ == 0)
{
lean_object* v___x_482_; 
lean_dec_ref(v_belowDict_425_);
lean_dec(v_cls_423_);
v___x_482_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_482_;
}
else
{
lean_object* v_inheritedTraceOptions_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_inheritedTraceOptions_483_ = lean_ctor_get(v_toCold_479_, 11);
v___x_484_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_423_);
v___x_485_ = l_Lean_Name_append(v___x_484_, v_cls_423_);
v___x_486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_483_, v_options_480_, v___x_485_);
lean_dec(v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_belowDict_425_);
lean_dec(v_cls_423_);
v___x_487_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_489_ = l_Lean_indentExpr(v_belowDict_425_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_423_, v___x_490_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; 
lean_dec_ref_known(v___x_491_, 1);
v___x_492_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_492_;
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_493_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_491_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_491_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v_a_524_, lean_object* v_C_525_, lean_object* v_cls_526_, lean_object* v___f_527_, lean_object* v_belowDict_528_, lean_object* v_F_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v_a_524_, v_C_525_, v_cls_526_, v___f_527_, v_belowDict_528_, v_F_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_C_525_);
return v_res_535_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0(void){
_start:
{
lean_object* v___x_536_; lean_object* v_dummy_537_; 
v___x_536_ = lean_box(0);
v_dummy_537_ = l_Lean_Expr_sort___override(v___x_536_);
return v_dummy_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_538_, lean_object* v_C_539_, lean_object* v_cls_540_, lean_object* v___f_541_, lean_object* v_F_542_, lean_object* v_xs_543_, lean_object* v_belowDict_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v___x_550_; lean_object* v___x_551_; 
v___x_550_ = 1;
v___x_551_ = l_Lean_Meta_zetaReduce(v_arg_538_, v___x_550_, v___x_550_, v___x_550_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___f_553_; lean_object* v_dummy_554_; lean_object* v_nargs_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc_n(v_a_552_, 2);
lean_dec_ref_known(v___x_551_, 1);
v___f_553_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed), 11, 4);
lean_closure_set(v___f_553_, 0, v_a_552_);
lean_closure_set(v___f_553_, 1, v_C_539_);
lean_closure_set(v___f_553_, 2, v_cls_540_);
lean_closure_set(v___f_553_, 3, v___f_541_);
v_dummy_554_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_555_ = l_Lean_Expr_getAppNumArgs(v_a_552_);
lean_inc(v_nargs_555_);
v___x_556_ = lean_mk_array(v_nargs_555_, v_dummy_554_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_sub(v_nargs_555_, v___x_557_);
lean_dec(v_nargs_555_);
v___x_559_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_552_, v___x_556_, v___x_558_);
v___x_572_ = lean_array_get_size(v_xs_543_);
v___x_573_ = lean_array_get_size(v___x_559_);
v___x_574_ = lean_nat_dec_le(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v___x_559_);
lean_dec_ref(v___f_553_);
lean_dec_ref(v_F_542_);
v___x_575_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_545_, v___y_546_, v___y_547_, v___y_548_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
v___y_561_ = v___y_545_;
v___y_562_ = v___y_546_;
v___y_563_ = v___y_547_;
v___y_564_ = v___y_548_;
goto v___jp_560_;
}
v___jp_560_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_565_ = lean_array_get_size(v___x_559_);
v___x_566_ = lean_array_get_size(v_xs_543_);
v___x_567_ = lean_nat_sub(v___x_565_, v___x_566_);
v___x_568_ = l_Array_extract___redArg(v___x_559_, v___x_567_, v___x_565_);
lean_dec_ref(v___x_559_);
v___x_569_ = l_Lean_Expr_replaceFVars(v_belowDict_544_, v_xs_543_, v___x_568_);
v___x_570_ = l_Lean_mkAppN(v_F_542_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_571_ = l_Lean_Elab_Structural_searchPProd___redArg(v___x_569_, v___x_570_, v___f_553_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_571_;
}
}
else
{
lean_dec_ref(v_F_542_);
lean_dec_ref(v___f_541_);
lean_dec(v_cls_540_);
lean_dec_ref(v_C_539_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_584_, lean_object* v_C_585_, lean_object* v_cls_586_, lean_object* v___f_587_, lean_object* v_F_588_, lean_object* v_xs_589_, lean_object* v_belowDict_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_584_, v_C_585_, v_cls_586_, v___f_587_, v_F_588_, v_xs_589_, v_belowDict_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec_ref(v_belowDict_590_);
lean_dec_ref(v_xs_589_);
return v_res_596_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v_arg_600_, lean_object* v_C_601_, lean_object* v_cls_602_, lean_object* v___f_603_, lean_object* v_belowDict_604_, lean_object* v_F_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___f_611_; lean_object* v___x_615_; 
lean_inc_ref(v___f_603_);
lean_inc(v_cls_602_);
v___f_611_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_611_, 0, v_arg_600_);
lean_closure_set(v___f_611_, 1, v_C_601_);
lean_closure_set(v___f_611_, 2, v_cls_602_);
lean_closure_set(v___f_611_, 3, v___f_603_);
lean_closure_set(v___f_611_, 4, v_F_605_);
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
lean_inc(v___y_607_);
lean_inc_ref(v___y_606_);
v___x_615_ = lean_apply_5(v___f_603_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, lean_box(0));
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; uint8_t v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
if (v___x_617_ == 0)
{
lean_dec(v_cls_602_);
goto v___jp_612_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_618_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_604_);
v___x_619_ = l_Lean_indentExpr(v_belowDict_604_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_602_, v___x_620_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_dec_ref_known(v___x_621_, 1);
goto v___jp_612_;
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v___f_611_);
lean_dec_ref(v_belowDict_604_);
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v___f_611_);
lean_dec_ref(v_belowDict_604_);
lean_dec(v_cls_602_);
v_a_630_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_615_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_615_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
v___jp_612_:
{
uint8_t v___x_613_; lean_object* v___x_614_; 
v___x_613_ = 0;
v___x_614_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_604_, v___f_611_, v___x_613_, v___x_613_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v_arg_638_, lean_object* v_C_639_, lean_object* v_cls_640_, lean_object* v___f_641_, lean_object* v_belowDict_642_, lean_object* v_F_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v_arg_638_, v_C_639_, v_cls_640_, v___f_641_, v_belowDict_642_, v_F_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_649_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_661_ = l_Lean_stringToMessageData(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_665_, lean_object* v_belowDict_666_, lean_object* v_arg_667_, lean_object* v_F_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_cls_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v_a_678_; uint8_t v___x_679_; 
v_cls_674_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_675_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
lean_inc_ref(v_arg_667_);
v___f_676_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_676_, 0, v_arg_667_);
lean_closure_set(v___f_676_, 1, v_C_665_);
lean_closure_set(v___f_676_, 2, v_cls_674_);
lean_closure_set(v___f_676_, 3, v___f_675_);
v___x_677_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_674_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref(v___x_677_);
v___x_679_ = lean_unbox(v_a_678_);
lean_dec(v_a_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec_ref(v_arg_667_);
v___x_680_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_666_, v_F_668_, v___f_676_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_681_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_666_);
v___x_682_ = l_Lean_indentExpr(v_belowDict_666_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_indentExpr(v_arg_667_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_674_, v___x_687_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_689_; 
lean_dec_ref_known(v___x_688_, 1);
v___x_689_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_666_, v_F_668_, v___f_676_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
return v___x_689_;
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v___f_676_);
lean_dec_ref(v_F_668_);
lean_dec_ref(v_belowDict_666_);
v_a_690_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_688_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_688_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_698_, lean_object* v_belowDict_699_, lean_object* v_arg_700_, lean_object* v_F_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_698_, v_belowDict_699_, v_arg_700_, v_F_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v_t_708_, lean_object* v_x_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_t_708_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v_t_716_, lean_object* v_x_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v_t_716_, v_x_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec_ref(v_x_717_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___f_733_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_733_, 0, v_t_727_);
v___x_734_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1));
v___x_735_ = l_Lean_Core_mkFreshUserName(v___x_734_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_a_736_);
lean_ctor_set(v___x_740_, 1, v___f_733_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v___f_733_);
v_a_745_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_735_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_735_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v___x_760_, lean_object* v_a_761_, lean_object* v_x_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_array_set(v___y_763_, v_a_761_, v___x_760_);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v___x_772_, lean_object* v_a_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v___x_772_, v_a_773_, v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v_a_773_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_782_, lean_object* v_a_783_, lean_object* v_x_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_snd_791_; lean_object* v_fst_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_843_; 
v_snd_791_ = lean_ctor_get(v___y_785_, 1);
v_fst_792_ = lean_ctor_get(v___y_785_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___y_785_);
if (v_isSharedCheck_843_ == 0)
{
v___x_794_ = v___y_785_;
v_isShared_795_ = v_isSharedCheck_843_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_snd_791_);
lean_inc(v_fst_792_);
lean_dec(v___y_785_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_843_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_array_796_; lean_object* v_start_797_; lean_object* v_stop_798_; uint8_t v___x_799_; 
v_array_796_ = lean_ctor_get(v_snd_791_, 0);
v_start_797_ = lean_ctor_get(v_snd_791_, 1);
v_stop_798_ = lean_ctor_get(v_snd_791_, 2);
v___x_799_ = lean_nat_dec_lt(v_start_797_, v_stop_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_801_; 
lean_dec_ref(v_a_783_);
lean_dec_ref(v___x_782_);
if (v_isShared_795_ == 0)
{
v___x_801_ = v___x_794_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_fst_792_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_snd_791_);
v___x_801_ = v_reuseFailAlloc_804_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
else
{
lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_839_; 
lean_inc(v_stop_798_);
lean_inc(v_start_797_);
lean_inc_ref(v_array_796_);
v_isSharedCheck_839_ = !lean_is_exclusive(v_snd_791_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_840_ = lean_ctor_get(v_snd_791_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_snd_791_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_snd_791_, 0);
lean_dec(v_unused_842_);
v___x_806_ = v_snd_791_;
v_isShared_807_ = v_isSharedCheck_839_;
goto v_resetjp_805_;
}
else
{
lean_dec(v_snd_791_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_839_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_808_ = lean_array_fget_borrowed(v_array_796_, v_start_797_);
lean_inc(v___x_808_);
v___f_809_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_809_, 0, v___x_808_);
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_start_797_, v___x_810_);
lean_dec(v_start_797_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_811_);
v___x_813_ = v___x_806_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_array_796_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_stop_798_);
v___x_813_ = v_reuseFailAlloc_838_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
size_t v_sz_814_; size_t v___x_815_; lean_object* v___x_7263__overap_816_; lean_object* v___x_817_; 
v_sz_814_ = lean_array_size(v_a_783_);
v___x_815_ = ((size_t)0ULL);
v___x_7263__overap_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_782_, v_a_783_, v___f_809_, v_sz_814_, v___x_815_, v_fst_792_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
v___x_817_ = lean_apply_5(v___x_7263__overap_816_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, lean_box(0));
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_829_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_829_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_829_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_829_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_813_);
lean_ctor_set(v___x_794_, 0, v_a_818_);
v___x_823_ = v___x_794_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_818_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_813_);
v___x_823_ = v_reuseFailAlloc_828_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_824_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___x_813_);
lean_del_object(v___x_794_);
v_a_830_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_817_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_817_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_844_, lean_object* v_a_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_844_, v_a_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_toCold_860_; lean_object* v_options_861_; uint8_t v_hasTrace_862_; 
v_toCold_860_ = lean_ctor_get(v___y_857_, 0);
v_options_861_ = lean_ctor_get(v_toCold_860_, 2);
v_hasTrace_862_ = lean_ctor_get_uint8(v_options_861_, sizeof(void*)*1);
if (v_hasTrace_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v___x_854_);
v___x_863_ = lean_box(v_hasTrace_862_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
else
{
lean_object* v_inheritedTraceOptions_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_inheritedTraceOptions_865_ = lean_ctor_get(v_toCold_860_, 11);
v___x_866_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_867_ = l_Lean_Name_append(v___x_866_, v___x_854_);
v___x_868_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_865_, v_options_861_, v___x_867_);
lean_dec(v___x_867_);
v___x_869_ = lean_box(v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_877_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_889_, lean_object* v___x_890_, lean_object* v_positions_891_, lean_object* v_a_892_, lean_object* v___x_893_, lean_object* v___x_894_, lean_object* v_k_895_, lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v_toMonadRef_898_, lean_object* v___x_899_, lean_object* v___f_900_, lean_object* v_Cs_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; lean_object* v___x_7299__overap_908_; lean_object* v___x_909_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_901_);
lean_inc_ref(v___x_889_);
v___x_7299__overap_908_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_889_, v___x_890_, v___x_907_, v_positions_891_, v_a_892_, v_Cs_901_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
v___x_909_ = lean_apply_5(v___x_7299__overap_908_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, lean_box(0));
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___x_952_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v___x_911_ = l_Lean_mkAppN(v___x_893_, v_a_910_);
lean_dec(v_a_910_);
v___x_912_ = l_Subarray_copy___redArg(v___x_894_);
v___x_913_ = l_Lean_mkAppN(v___x_911_, v___x_912_);
lean_dec_ref(v___x_912_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
v___x_952_ = lean_apply_5(v___f_900_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, lean_box(0));
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; uint8_t v___x_954_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = lean_unbox(v_a_953_);
lean_dec(v_a_953_);
if (v___x_954_ == 0)
{
v___y_915_ = v___y_902_;
v___y_916_ = v___y_903_;
v___y_917_ = v___y_904_;
v___y_918_ = v___y_905_;
goto v___jp_914_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_7349__overap_966_; lean_object* v___x_967_; 
v___x_955_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_Cs_901_);
v___x_956_ = lean_array_to_list(v_Cs_901_);
v___x_957_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_958_ = lean_box(0);
v___x_959_ = l_List_mapTR_loop___redArg(v___x_957_, v___x_956_, v___x_958_);
v___x_960_ = l_Lean_MessageData_ofList(v___x_959_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_955_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
lean_inc_ref(v___x_913_);
v___x_964_ = l_Lean_indentExpr(v___x_913_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
lean_inc(v___x_896_);
lean_inc_ref(v___x_899_);
lean_inc_ref(v_toMonadRef_898_);
lean_inc_ref(v___x_897_);
lean_inc_ref(v___x_889_);
v___x_7349__overap_966_ = l_Lean_addTrace___redArg(v___x_889_, v___x_897_, v_toMonadRef_898_, v___x_899_, v___x_896_, v___x_965_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
v___x_967_ = lean_apply_5(v___x_7349__overap_966_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, lean_box(0));
if (lean_obj_tag(v___x_967_) == 0)
{
lean_dec_ref_known(v___x_967_, 1);
v___y_915_ = v___y_902_;
v___y_916_ = v___y_903_;
v___y_917_ = v___y_904_;
v___y_918_ = v___y_905_;
goto v___jp_914_;
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v___x_913_);
lean_dec_ref(v_Cs_901_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v_toMonadRef_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
lean_dec_ref(v_k_895_);
lean_dec_ref(v___x_889_);
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v___x_913_);
lean_dec_ref(v_Cs_901_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v_toMonadRef_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
lean_dec_ref(v_k_895_);
lean_dec_ref(v___x_889_);
v_a_976_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_952_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_952_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
v___jp_914_:
{
lean_object* v___x_919_; 
lean_inc_ref(v___x_913_);
v___x_919_ = l_Lean_Meta_isTypeCorrect(v___x_913_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; uint8_t v___x_921_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = lean_unbox(v_a_920_);
lean_dec(v_a_920_);
if (v___x_921_ == 0)
{
lean_object* v_toCold_922_; lean_object* v_options_923_; uint8_t v_hasTrace_924_; 
v_toCold_922_ = lean_ctor_get(v___y_917_, 0);
v_options_923_ = lean_ctor_get(v_toCold_922_, 2);
v_hasTrace_924_ = lean_ctor_get_uint8(v_options_923_, sizeof(void*)*1);
if (v_hasTrace_924_ == 0)
{
lean_object* v___x_925_; 
lean_dec_ref(v___x_899_);
lean_dec_ref(v_toMonadRef_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
lean_dec_ref(v___x_889_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
v___x_925_ = lean_apply_7(v_k_895_, v_Cs_901_, v___x_913_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
return v___x_925_;
}
else
{
lean_object* v_inheritedTraceOptions_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_inheritedTraceOptions_926_ = lean_ctor_get(v_toCold_922_, 11);
v___x_927_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_896_);
v___x_928_ = l_Lean_Name_append(v___x_927_, v___x_896_);
v___x_929_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_926_, v_options_923_, v___x_928_);
lean_dec(v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v___x_899_);
lean_dec_ref(v_toMonadRef_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
lean_dec_ref(v___x_889_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
v___x_930_ = lean_apply_7(v_k_895_, v_Cs_901_, v___x_913_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_7322__overap_932_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
v___x_7322__overap_932_ = l_Lean_addTrace___redArg(v___x_889_, v___x_897_, v_toMonadRef_898_, v___x_899_, v___x_896_, v___x_931_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
v___x_933_ = lean_apply_5(v___x_7322__overap_932_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; 
lean_dec_ref_known(v___x_933_, 1);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
v___x_934_ = lean_apply_7(v_k_895_, v_Cs_901_, v___x_913_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
return v___x_934_;
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v___x_913_);
lean_dec_ref(v_Cs_901_);
lean_dec_ref(v_k_895_);
v_a_935_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_933_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v___x_899_);
lean_dec_ref(v_toMonadRef_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
lean_dec_ref(v___x_889_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
v___x_943_ = lean_apply_7(v_k_895_, v_Cs_901_, v___x_913_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
return v___x_943_;
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v___x_913_);
lean_dec_ref(v_Cs_901_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v_toMonadRef_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
lean_dec_ref(v_k_895_);
lean_dec_ref(v___x_889_);
v_a_944_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_919_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_919_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_Cs_901_);
lean_dec_ref(v___f_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v_toMonadRef_898_);
lean_dec_ref(v___x_897_);
lean_dec(v___x_896_);
lean_dec_ref(v_k_895_);
lean_dec_ref(v___x_894_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_889_);
v_a_984_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_909_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_909_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_992_ = _args[0];
lean_object* v___x_993_ = _args[1];
lean_object* v_positions_994_ = _args[2];
lean_object* v_a_995_ = _args[3];
lean_object* v___x_996_ = _args[4];
lean_object* v___x_997_ = _args[5];
lean_object* v_k_998_ = _args[6];
lean_object* v___x_999_ = _args[7];
lean_object* v___x_1000_ = _args[8];
lean_object* v_toMonadRef_1001_ = _args[9];
lean_object* v___x_1002_ = _args[10];
lean_object* v___f_1003_ = _args[11];
lean_object* v_Cs_1004_ = _args[12];
lean_object* v___y_1005_ = _args[13];
lean_object* v___y_1006_ = _args[14];
lean_object* v___y_1007_ = _args[15];
lean_object* v___y_1008_ = _args[16];
lean_object* v___y_1009_ = _args[17];
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_992_, v___x_993_, v_positions_994_, v_a_995_, v___x_996_, v___x_997_, v_k_998_, v___x_999_, v___x_1000_, v_toMonadRef_1001_, v___x_1002_, v___f_1003_, v_Cs_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1010_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_unsigned_to_nat(37u);
v___x_1012_ = l_Lean_Level_ofNat(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1014_ = l_Lean_Expr_sort___override(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1021_, lean_object* v___x_1022_, lean_object* v___f_1023_, lean_object* v___f_1024_, lean_object* v___x_1025_, lean_object* v_numTypeFormers_1026_, lean_object* v___x_1027_, lean_object* v_k_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v_toMonadRef_1031_, lean_object* v___x_1032_, lean_object* v___f_1033_, lean_object* v_numIndParams_1034_, lean_object* v_a_1035_, lean_object* v_f_1036_, lean_object* v_args_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v_lower_1093_; lean_object* v_upper_1094_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1160_ = lean_nat_add(v_numIndParams_1034_, v_numTypeFormers_1026_);
v___x_1161_ = lean_array_get_size(v_args_1037_);
v___x_1162_ = lean_nat_dec_lt(v___x_1160_, v___x_1161_);
lean_dec(v___x_1160_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_dec_ref(v_args_1037_);
lean_dec_ref(v_f_1036_);
lean_dec(v_numIndParams_1034_);
lean_dec_ref(v_k_1028_);
lean_dec_ref(v___x_1027_);
lean_dec(v_numTypeFormers_1026_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___f_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v_positions_1021_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
v___x_1163_ = lean_apply_5(v___f_1033_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, lean_box(0));
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; uint8_t v___x_1165_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = lean_unbox(v_a_1164_);
lean_dec(v_a_1164_);
if (v___x_1165_ == 0)
{
lean_dec_ref(v_a_1035_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_toMonadRef_1031_);
lean_dec_ref(v___x_1030_);
lean_dec(v___x_1029_);
lean_dec_ref(v___x_1022_);
v___y_1147_ = v___y_1038_;
v___y_1148_ = v___y_1039_;
v___y_1149_ = v___y_1040_;
v___y_1150_ = v___y_1041_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_7478__overap_1169_; lean_object* v___x_1170_; 
v___x_1166_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1167_ = l_Lean_indentExpr(v_a_1035_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_7478__overap_1169_ = l_Lean_addTrace___redArg(v___x_1022_, v___x_1030_, v_toMonadRef_1031_, v___x_1032_, v___x_1029_, v___x_1168_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
v___x_1170_ = lean_apply_5(v___x_7478__overap_1169_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, lean_box(0));
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_dec_ref_known(v___x_1170_, 1);
v___y_1147_ = v___y_1038_;
v___y_1148_ = v___y_1039_;
v___y_1149_ = v___y_1040_;
v___y_1150_ = v___y_1041_;
goto v___jp_1146_;
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_a_1035_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_toMonadRef_1031_);
lean_dec_ref(v___x_1030_);
lean_dec(v___x_1029_);
lean_dec_ref(v___x_1022_);
v_a_1179_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1163_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1163_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_dec_ref(v_a_1035_);
v___y_1137_ = v___y_1038_;
v___y_1138_ = v___y_1039_;
v___y_1139_ = v___y_1040_;
v___y_1140_ = v___y_1041_;
goto v___jp_1136_;
}
v___jp_1043_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; size_t v_sz_1057_; size_t v___x_1058_; lean_object* v___x_7394__overap_1059_; lean_object* v___x_1060_; 
v___x_1052_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1053_ = lean_mk_array(v___y_1045_, v___x_1052_);
v___x_1054_ = lean_array_get_size(v___y_1044_);
v___x_1055_ = l_Array_toSubarray___redArg(v___y_1044_, v___y_1046_, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1053_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v_sz_1057_ = lean_array_size(v_positions_1021_);
v___x_1058_ = ((size_t)0ULL);
lean_inc_ref(v___x_1022_);
v___x_7394__overap_1059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1022_, v_positions_1021_, v___f_1023_, v_sz_1057_, v___x_1058_, v___x_1056_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1060_ = lean_apply_5(v___x_7394__overap_1059_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v_fst_1062_; size_t v_sz_1063_; lean_object* v___x_7397__overap_1064_; lean_object* v___x_1065_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v_fst_1062_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_fst_1062_);
lean_dec(v_a_1061_);
v_sz_1063_ = lean_array_size(v_fst_1062_);
lean_inc_ref(v___x_1022_);
v___x_7397__overap_1064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1022_, v___f_1024_, v_sz_1063_, v___x_1058_, v_fst_1062_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1065_ = lean_apply_5(v___x_7397__overap_1064_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; uint8_t v___x_1067_; lean_object* v___x_7401__overap_1068_; lean_object* v___x_1069_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = 0;
v___x_7401__overap_1068_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1025_, v___x_1022_, v_a_1066_, v___y_1047_, v___x_1067_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1069_ = lean_apply_5(v___x_7401__overap_1068_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
return v___x_1069_;
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v___y_1047_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___x_1022_);
v_a_1070_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1065_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1065_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v___y_1047_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___f_1024_);
lean_dec_ref(v___x_1022_);
v_a_1078_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1060_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1060_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
v___jp_1086_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1095_ = l_Array_toSubarray___redArg(v_args_1037_, v_lower_1093_, v_upper_1094_);
v___x_1096_ = l_Subarray_copy___redArg(v___y_1091_);
v___x_1097_ = l_Lean_mkAppN(v_f_1036_, v___x_1096_);
lean_dec_ref(v___x_1096_);
lean_inc_ref(v___x_1097_);
v___x_1098_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1026_, v___x_1097_, v___y_1090_, v___y_1087_, v___y_1088_, v___y_1089_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_n(v_a_1099_, 2);
lean_dec_ref_known(v___x_1098_, 1);
lean_inc_ref(v___f_1033_);
lean_inc_ref(v___x_1032_);
lean_inc_ref(v_toMonadRef_1031_);
lean_inc_ref(v___x_1030_);
lean_inc(v___x_1029_);
lean_inc_ref(v_positions_1021_);
lean_inc_ref(v___x_1022_);
v___f_1100_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1100_, 0, v___x_1022_);
lean_closure_set(v___f_1100_, 1, v___x_1027_);
lean_closure_set(v___f_1100_, 2, v_positions_1021_);
lean_closure_set(v___f_1100_, 3, v_a_1099_);
lean_closure_set(v___f_1100_, 4, v___x_1097_);
lean_closure_set(v___f_1100_, 5, v___x_1095_);
lean_closure_set(v___f_1100_, 6, v_k_1028_);
lean_closure_set(v___f_1100_, 7, v___x_1029_);
lean_closure_set(v___f_1100_, 8, v___x_1030_);
lean_closure_set(v___f_1100_, 9, v_toMonadRef_1031_);
lean_closure_set(v___f_1100_, 10, v___x_1032_);
lean_closure_set(v___f_1100_, 11, v___f_1033_);
v___x_1101_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1021_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1090_);
v___x_1102_ = lean_apply_5(v___f_1033_, v___y_1090_, v___y_1087_, v___y_1088_, v___y_1089_, lean_box(0));
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; uint8_t v___x_1104_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1104_ = lean_unbox(v_a_1103_);
lean_dec(v_a_1103_);
if (v___x_1104_ == 0)
{
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_toMonadRef_1031_);
lean_dec_ref(v___x_1030_);
lean_dec(v___x_1029_);
v___y_1044_ = v_a_1099_;
v___y_1045_ = v___x_1101_;
v___y_1046_ = v___y_1092_;
v___y_1047_ = v___f_1100_;
v___y_1048_ = v___y_1090_;
v___y_1049_ = v___y_1087_;
v___y_1050_ = v___y_1088_;
v___y_1051_ = v___y_1089_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_7433__overap_1110_; lean_object* v___x_1111_; 
v___x_1105_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1101_);
v___x_1106_ = l_Nat_reprFast(v___x_1101_);
v___x_1107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
v___x_1108_ = l_Lean_MessageData_ofFormat(v___x_1107_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1105_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
lean_inc_ref(v___x_1022_);
v___x_7433__overap_1110_ = l_Lean_addTrace___redArg(v___x_1022_, v___x_1030_, v_toMonadRef_1031_, v___x_1032_, v___x_1029_, v___x_1109_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1090_);
v___x_1111_ = lean_apply_5(v___x_7433__overap_1110_, v___y_1090_, v___y_1087_, v___y_1088_, v___y_1089_, lean_box(0));
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_dec_ref_known(v___x_1111_, 1);
v___y_1044_ = v_a_1099_;
v___y_1045_ = v___x_1101_;
v___y_1046_ = v___y_1092_;
v___y_1047_ = v___f_1100_;
v___y_1048_ = v___y_1090_;
v___y_1049_ = v___y_1087_;
v___y_1050_ = v___y_1088_;
v___y_1051_ = v___y_1089_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v___x_1101_);
lean_dec_ref(v___f_1100_);
lean_dec(v_a_1099_);
lean_dec(v___y_1092_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___f_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v___x_1022_);
lean_dec_ref(v_positions_1021_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
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
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v___x_1101_);
lean_dec_ref(v___f_1100_);
lean_dec(v_a_1099_);
lean_dec(v___y_1092_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_toMonadRef_1031_);
lean_dec_ref(v___x_1030_);
lean_dec(v___x_1029_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___f_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v___x_1022_);
lean_dec_ref(v_positions_1021_);
v_a_1120_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1102_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1102_);
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
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v___x_1097_);
lean_dec_ref(v___x_1095_);
lean_dec(v___y_1092_);
lean_dec_ref(v___f_1033_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_toMonadRef_1031_);
lean_dec_ref(v___x_1030_);
lean_dec(v___x_1029_);
lean_dec_ref(v_k_1028_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v___f_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v___x_1022_);
lean_dec_ref(v_positions_1021_);
v_a_1128_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1098_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1098_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
v___jp_1136_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1034_);
lean_inc_ref(v_args_1037_);
v___x_1142_ = l_Array_toSubarray___redArg(v_args_1037_, v___x_1141_, v_numIndParams_1034_);
v___x_1143_ = lean_nat_add(v_numIndParams_1034_, v_numTypeFormers_1026_);
lean_dec(v_numIndParams_1034_);
v___x_1144_ = lean_array_get_size(v_args_1037_);
v___x_1145_ = lean_nat_dec_le(v___x_1143_, v___x_1141_);
if (v___x_1145_ == 0)
{
v___y_1087_ = v___y_1138_;
v___y_1088_ = v___y_1139_;
v___y_1089_ = v___y_1140_;
v___y_1090_ = v___y_1137_;
v___y_1091_ = v___x_1142_;
v___y_1092_ = v___x_1141_;
v_lower_1093_ = v___x_1143_;
v_upper_1094_ = v___x_1144_;
goto v___jp_1086_;
}
else
{
lean_dec(v___x_1143_);
v___y_1087_ = v___y_1138_;
v___y_1088_ = v___y_1139_;
v___y_1089_ = v___y_1140_;
v___y_1090_ = v___y_1137_;
v___y_1091_ = v___x_1142_;
v___y_1092_ = v___x_1141_;
v_lower_1093_ = v___x_1141_;
v_upper_1094_ = v___x_1144_;
goto v___jp_1086_;
}
}
v___jp_1146_:
{
lean_object* v___x_1151_; lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v___x_1151_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1187_ = _args[0];
lean_object* v___x_1188_ = _args[1];
lean_object* v___f_1189_ = _args[2];
lean_object* v___f_1190_ = _args[3];
lean_object* v___x_1191_ = _args[4];
lean_object* v_numTypeFormers_1192_ = _args[5];
lean_object* v___x_1193_ = _args[6];
lean_object* v_k_1194_ = _args[7];
lean_object* v___x_1195_ = _args[8];
lean_object* v___x_1196_ = _args[9];
lean_object* v_toMonadRef_1197_ = _args[10];
lean_object* v___x_1198_ = _args[11];
lean_object* v___f_1199_ = _args[12];
lean_object* v_numIndParams_1200_ = _args[13];
lean_object* v_a_1201_ = _args[14];
lean_object* v_f_1202_ = _args[15];
lean_object* v_args_1203_ = _args[16];
lean_object* v___y_1204_ = _args[17];
lean_object* v___y_1205_ = _args[18];
lean_object* v___y_1206_ = _args[19];
lean_object* v___y_1207_ = _args[20];
lean_object* v___y_1208_ = _args[21];
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1187_, v___x_1188_, v___f_1189_, v___f_1190_, v___x_1191_, v_numTypeFormers_1192_, v___x_1193_, v_k_1194_, v___x_1195_, v___x_1196_, v_toMonadRef_1197_, v___x_1198_, v___f_1199_, v_numIndParams_1200_, v_a_1201_, v_f_1202_, v_args_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_instMonadEIO___redArg();
return v___x_1210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1212_ = l_StateRefT_x27_instMonad___redArg(v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1220_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1221_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1220_, v___x_1219_);
return v___x_1221_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1224_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1223_, v___x_1222_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1228_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1229_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
v___x_1230_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1229_, v___x_1228_, v___x_1227_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1232_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1234_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1233_, v___f_1232_, v___x_1231_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16));
v___x_1240_ = l_Lean_stringToMessageData(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1241_, lean_object* v_numIndParams_1242_, lean_object* v_positions_1243_, lean_object* v_k_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1250_; lean_object* v_toApplicative_1251_; lean_object* v_toFunctor_1252_; lean_object* v_toSeq_1253_; lean_object* v_toSeqLeft_1254_; lean_object* v_toSeqRight_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_toApplicative_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1389_; 
v___x_1250_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1251_ = lean_ctor_get(v___x_1250_, 0);
v_toFunctor_1252_ = lean_ctor_get(v_toApplicative_1251_, 0);
v_toSeq_1253_ = lean_ctor_get(v_toApplicative_1251_, 2);
v_toSeqLeft_1254_ = lean_ctor_get(v_toApplicative_1251_, 3);
v_toSeqRight_1255_ = lean_ctor_get(v_toApplicative_1251_, 4);
v___f_1256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1257_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1252_, 2);
v___f_1258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1258_, 0, v_toFunctor_1252_);
v___f_1259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1259_, 0, v_toFunctor_1252_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___f_1258_);
lean_ctor_set(v___x_1260_, 1, v___f_1259_);
lean_inc(v_toSeqRight_1255_);
v___f_1261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1261_, 0, v_toSeqRight_1255_);
lean_inc(v_toSeqLeft_1254_);
v___f_1262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1262_, 0, v_toSeqLeft_1254_);
lean_inc(v_toSeq_1253_);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toSeq_1253_);
v___x_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1260_);
lean_ctor_set(v___x_1264_, 1, v___f_1256_);
lean_ctor_set(v___x_1264_, 2, v___f_1263_);
lean_ctor_set(v___x_1264_, 3, v___f_1262_);
lean_ctor_set(v___x_1264_, 4, v___f_1261_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v___f_1257_);
v___x_1266_ = l_StateRefT_x27_instMonad___redArg(v___x_1265_);
v_toApplicative_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v___x_1266_, 1);
lean_dec(v_unused_1390_);
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1389_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_toApplicative_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1389_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v_toFunctor_1271_; lean_object* v_toSeq_1272_; lean_object* v_toSeqLeft_1273_; lean_object* v_toSeqRight_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1387_; 
v_toFunctor_1271_ = lean_ctor_get(v_toApplicative_1267_, 0);
v_toSeq_1272_ = lean_ctor_get(v_toApplicative_1267_, 2);
v_toSeqLeft_1273_ = lean_ctor_get(v_toApplicative_1267_, 3);
v_toSeqRight_1274_ = lean_ctor_get(v_toApplicative_1267_, 4);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_toApplicative_1267_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v_toApplicative_1267_, 1);
lean_dec(v_unused_1388_);
v___x_1276_ = v_toApplicative_1267_;
v_isShared_1277_ = v_isSharedCheck_1387_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_toSeqRight_1274_);
lean_inc(v_toSeqLeft_1273_);
lean_inc(v_toSeq_1272_);
lean_inc(v_toFunctor_1271_);
lean_dec(v_toApplicative_1267_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1387_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___f_1278_; lean_object* v___f_1279_; lean_object* v___f_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; lean_object* v___f_1284_; lean_object* v___f_1285_; lean_object* v___x_1287_; 
v___f_1278_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1271_);
v___f_1280_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1280_, 0, v_toFunctor_1271_);
v___f_1281_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1281_, 0, v_toFunctor_1271_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___f_1280_);
lean_ctor_set(v___x_1282_, 1, v___f_1281_);
v___f_1283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1283_, 0, v_toSeqRight_1274_);
v___f_1284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1284_, 0, v_toSeqLeft_1273_);
v___f_1285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1285_, 0, v_toSeq_1272_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 4, v___f_1283_);
lean_ctor_set(v___x_1276_, 3, v___f_1284_);
lean_ctor_set(v___x_1276_, 2, v___f_1285_);
lean_ctor_set(v___x_1276_, 1, v___f_1278_);
lean_ctor_set(v___x_1276_, 0, v___x_1282_);
v___x_1287_ = v___x_1276_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___f_1278_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v___f_1285_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v___f_1284_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v___f_1283_);
v___x_1287_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v___f_1279_);
lean_ctor_set(v___x_1269_, 0, v___x_1287_);
v___x_1289_ = v___x_1269_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___f_1279_);
v___x_1289_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v_toApplicative_1291_; lean_object* v_toFunctor_1292_; lean_object* v_toSeq_1293_; lean_object* v_toSeqLeft_1294_; lean_object* v_toSeqRight_1295_; lean_object* v___f_1296_; lean_object* v___f_1297_; lean_object* v___x_1298_; lean_object* v___f_1299_; lean_object* v___f_1300_; lean_object* v___f_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_toMonadRef_1308_; lean_object* v___f_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_numTypeFormers_1313_; lean_object* v___x_1314_; 
v___x_1290_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1291_ = lean_ctor_get(v___x_1250_, 0);
v_toFunctor_1292_ = lean_ctor_get(v_toApplicative_1291_, 0);
v_toSeq_1293_ = lean_ctor_get(v_toApplicative_1291_, 2);
v_toSeqLeft_1294_ = lean_ctor_get(v_toApplicative_1291_, 3);
v_toSeqRight_1295_ = lean_ctor_get(v_toApplicative_1291_, 4);
lean_inc_ref_n(v_toFunctor_1292_, 2);
v___f_1296_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1296_, 0, v_toFunctor_1292_);
v___f_1297_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1297_, 0, v_toFunctor_1292_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___f_1296_);
lean_ctor_set(v___x_1298_, 1, v___f_1297_);
lean_inc(v_toSeqRight_1295_);
v___f_1299_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1299_, 0, v_toSeqRight_1295_);
lean_inc(v_toSeqLeft_1294_);
v___f_1300_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1300_, 0, v_toSeqLeft_1294_);
lean_inc(v_toSeq_1293_);
v___f_1301_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1301_, 0, v_toSeq_1293_);
v___x_1302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1298_);
lean_ctor_set(v___x_1302_, 1, v___f_1256_);
lean_ctor_set(v___x_1302_, 2, v___f_1301_);
lean_ctor_set(v___x_1302_, 3, v___f_1300_);
lean_ctor_set(v___x_1302_, 4, v___f_1299_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___f_1257_);
v___x_1304_ = l_StateRefT_x27_instMonad___redArg(v___x_1303_);
v___x_1305_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1305_, 0, lean_box(0));
lean_closure_set(v___x_1305_, 1, lean_box(0));
lean_closure_set(v___x_1305_, 2, v___x_1304_);
v___x_1306_ = l_instMonadControlTOfPure___redArg(v___x_1305_);
v___x_1307_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1308_ = lean_ctor_get(v___x_1307_, 0);
v___f_1309_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
lean_inc_ref(v___x_1289_);
v___f_1310_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_1310_, 0, v___x_1289_);
v___x_1311_ = l_Lean_instInhabitedExpr;
v___x_1312_ = l_Lean_Meta_instAddMessageContextMetaM;
v_numTypeFormers_1313_ = lean_array_get_size(v_positions_1243_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
lean_inc_ref(v_below_1241_);
v___x_1314_ = lean_infer_type(v_below_1241_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___x_1361_; lean_object* v_a_1362_; uint8_t v___x_1363_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_n(v_a_1315_, 2);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15));
lean_inc_ref(v_toMonadRef_1308_);
lean_inc_ref(v___x_1289_);
v___f_1318_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1318_, 0, v_positions_1243_);
lean_closure_set(v___f_1318_, 1, v___x_1289_);
lean_closure_set(v___f_1318_, 2, v___f_1310_);
lean_closure_set(v___f_1318_, 3, v___f_1309_);
lean_closure_set(v___f_1318_, 4, v___x_1306_);
lean_closure_set(v___f_1318_, 5, v_numTypeFormers_1313_);
lean_closure_set(v___f_1318_, 6, v___x_1311_);
lean_closure_set(v___f_1318_, 7, v_k_1244_);
lean_closure_set(v___f_1318_, 8, v___x_1316_);
lean_closure_set(v___f_1318_, 9, v___x_1290_);
lean_closure_set(v___f_1318_, 10, v_toMonadRef_1308_);
lean_closure_set(v___f_1318_, 11, v___x_1312_);
lean_closure_set(v___f_1318_, 12, v___f_1317_);
lean_closure_set(v___f_1318_, 13, v_numIndParams_1242_);
lean_closure_set(v___f_1318_, 14, v_a_1315_);
v___x_1361_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1316_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = lean_unbox(v_a_1362_);
lean_dec(v_a_1362_);
if (v___x_1363_ == 0)
{
v___y_1332_ = v_a_1245_;
v___y_1333_ = v_a_1246_;
v___y_1334_ = v_a_1247_;
v___y_1335_ = v_a_1248_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_7091__overap_1367_; lean_object* v___x_1368_; 
v___x_1364_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17);
lean_inc(v_a_1315_);
v___x_1365_ = l_Lean_MessageData_ofExpr(v_a_1315_);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
lean_inc_ref(v_toMonadRef_1308_);
lean_inc_ref(v___x_1289_);
v___x_7091__overap_1367_ = l_Lean_addTrace___redArg(v___x_1289_, v___x_1290_, v_toMonadRef_1308_, v___x_1312_, v___x_1316_, v___x_1366_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
v___x_1368_ = lean_apply_5(v___x_7091__overap_1367_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, lean_box(0));
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_dec_ref_known(v___x_1368_, 1);
v___y_1332_ = v_a_1245_;
v___y_1333_ = v_a_1246_;
v___y_1334_ = v_a_1247_;
v___y_1335_ = v_a_1248_;
goto v___jp_1331_;
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v___f_1318_);
lean_dec(v_a_1315_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v_below_1241_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
v___jp_1319_:
{
lean_object* v_dummy_1324_; lean_object* v_nargs_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_7087__overap_1329_; lean_object* v___x_1330_; 
v_dummy_1324_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1325_ = l_Lean_Expr_getAppNumArgs(v_a_1315_);
lean_inc(v_nargs_1325_);
v___x_1326_ = lean_mk_array(v_nargs_1325_, v_dummy_1324_);
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = lean_nat_sub(v_nargs_1325_, v___x_1327_);
lean_dec(v_nargs_1325_);
v___x_7087__overap_1329_ = l_Lean_Expr_withAppAux___redArg(v___f_1318_, v_a_1315_, v___x_1326_, v___x_1328_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
v___x_1330_ = lean_apply_5(v___x_7087__overap_1329_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, lean_box(0));
return v___x_1330_;
}
v___jp_1331_:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Meta_isTypeCorrect(v_below_1241_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; uint8_t v___x_1338_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1338_ = lean_unbox(v_a_1337_);
lean_dec(v_a_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v_a_1340_; uint8_t v___x_1341_; 
v___x_1339_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1316_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_unbox(v_a_1340_);
lean_dec(v_a_1340_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v___x_1289_);
v___y_1320_ = v___y_1332_;
v___y_1321_ = v___y_1333_;
v___y_1322_ = v___y_1334_;
v___y_1323_ = v___y_1335_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_7089__overap_1343_; lean_object* v___x_1344_; 
v___x_1342_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
lean_inc_ref(v_toMonadRef_1308_);
v___x_7089__overap_1343_ = l_Lean_addTrace___redArg(v___x_1289_, v___x_1290_, v_toMonadRef_1308_, v___x_1312_, v___x_1316_, v___x_1342_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
v___x_1344_ = lean_apply_5(v___x_7089__overap_1343_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, lean_box(0));
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_dec_ref_known(v___x_1344_, 1);
v___y_1320_ = v___y_1332_;
v___y_1321_ = v___y_1333_;
v___y_1322_ = v___y_1334_;
v___y_1323_ = v___y_1335_;
goto v___jp_1319_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v___f_1318_);
lean_dec(v_a_1315_);
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1289_);
v___y_1320_ = v___y_1332_;
v___y_1321_ = v___y_1333_;
v___y_1322_ = v___y_1334_;
v___y_1323_ = v___y_1335_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v___f_1318_);
lean_dec(v_a_1315_);
lean_dec_ref(v___x_1289_);
v_a_1353_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1336_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1336_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v___f_1310_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v_k_1244_);
lean_dec_ref(v_positions_1243_);
lean_dec(v_numIndParams_1242_);
lean_dec_ref(v_below_1241_);
v_a_1377_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1314_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1314_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1391_, lean_object* v_numIndParams_1392_, lean_object* v_positions_1393_, lean_object* v_k_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1391_, v_numIndParams_1392_, v_positions_1393_, v_k_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1401_, lean_object* v_inst_1402_, lean_object* v_below_1403_, lean_object* v_numIndParams_1404_, lean_object* v_positions_1405_, lean_object* v_k_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1403_, v_numIndParams_1404_, v_positions_1405_, v_k_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1413_, lean_object* v_inst_1414_, lean_object* v_below_1415_, lean_object* v_numIndParams_1416_, lean_object* v_positions_1417_, lean_object* v_k_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1413_, v_inst_1414_, v_below_1415_, v_numIndParams_1416_, v_positions_1417_, v_k_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_inst_1414_);
return v_res_1424_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_unsigned_to_nat(32u);
v___x_1426_ = lean_mk_empty_array_with_capacity(v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1428_ = ((size_t)5ULL);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_unsigned_to_nat(32u);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1430_);
v___x_1432_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1433_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___x_1431_);
lean_ctor_set(v___x_1433_, 2, v___x_1429_);
lean_ctor_set(v___x_1433_, 3, v___x_1429_);
lean_ctor_set_usize(v___x_1433_, 4, v___x_1428_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; lean_object* v_traceState_1437_; lean_object* v_traces_1438_; lean_object* v___x_1439_; lean_object* v_traceState_1440_; lean_object* v_env_1441_; lean_object* v_nextMacroScope_1442_; lean_object* v_ngen_1443_; lean_object* v_auxDeclNGen_1444_; lean_object* v_cache_1445_; lean_object* v_messages_1446_; lean_object* v_infoState_1447_; lean_object* v_snapshotTasks_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1467_; 
v___x_1436_ = lean_st_ref_get(v___y_1434_);
v_traceState_1437_ = lean_ctor_get(v___x_1436_, 4);
lean_inc_ref(v_traceState_1437_);
lean_dec(v___x_1436_);
v_traces_1438_ = lean_ctor_get(v_traceState_1437_, 0);
lean_inc_ref(v_traces_1438_);
lean_dec_ref(v_traceState_1437_);
v___x_1439_ = lean_st_ref_take(v___y_1434_);
v_traceState_1440_ = lean_ctor_get(v___x_1439_, 4);
v_env_1441_ = lean_ctor_get(v___x_1439_, 0);
v_nextMacroScope_1442_ = lean_ctor_get(v___x_1439_, 1);
v_ngen_1443_ = lean_ctor_get(v___x_1439_, 2);
v_auxDeclNGen_1444_ = lean_ctor_get(v___x_1439_, 3);
v_cache_1445_ = lean_ctor_get(v___x_1439_, 5);
v_messages_1446_ = lean_ctor_get(v___x_1439_, 6);
v_infoState_1447_ = lean_ctor_get(v___x_1439_, 7);
v_snapshotTasks_1448_ = lean_ctor_get(v___x_1439_, 8);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1450_ = v___x_1439_;
v_isShared_1451_ = v_isSharedCheck_1467_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_snapshotTasks_1448_);
lean_inc(v_infoState_1447_);
lean_inc(v_messages_1446_);
lean_inc(v_cache_1445_);
lean_inc(v_traceState_1440_);
lean_inc(v_auxDeclNGen_1444_);
lean_inc(v_ngen_1443_);
lean_inc(v_nextMacroScope_1442_);
lean_inc(v_env_1441_);
lean_dec(v___x_1439_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1467_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint64_t v_tid_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1465_; 
v_tid_1452_ = lean_ctor_get_uint64(v_traceState_1440_, sizeof(void*)*1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_traceState_1440_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_traceState_1440_, 0);
lean_dec(v_unused_1466_);
v___x_1454_ = v_traceState_1440_;
v_isShared_1455_ = v_isSharedCheck_1465_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_traceState_1440_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1465_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1456_);
v___x_1458_ = v___x_1454_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1456_);
lean_ctor_set_uint64(v_reuseFailAlloc_1464_, sizeof(void*)*1, v_tid_1452_);
v___x_1458_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 4, v___x_1458_);
v___x_1460_ = v___x_1450_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_env_1441_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_nextMacroScope_1442_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_ngen_1443_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_auxDeclNGen_1444_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1463_, 5, v_cache_1445_);
lean_ctor_set(v_reuseFailAlloc_1463_, 6, v_messages_1446_);
lean_ctor_set(v_reuseFailAlloc_1463_, 7, v_infoState_1447_);
lean_ctor_set(v_reuseFailAlloc_1463_, 8, v_snapshotTasks_1448_);
v___x_1460_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_st_ref_put(v___y_1434_, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_traces_1438_);
return v___x_1462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1468_);
lean_dec(v___y_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1482_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1483_, lean_object* v_opt_1484_){
_start:
{
lean_object* v_name_1485_; lean_object* v_defValue_1486_; lean_object* v_map_1487_; lean_object* v___x_1488_; 
v_name_1485_ = lean_ctor_get(v_opt_1484_, 0);
v_defValue_1486_ = lean_ctor_get(v_opt_1484_, 1);
v_map_1487_ = lean_ctor_get(v_opts_1483_, 0);
v___x_1488_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1487_, v_name_1485_);
if (lean_obj_tag(v___x_1488_) == 0)
{
uint8_t v___x_1489_; 
v___x_1489_ = lean_unbox(v_defValue_1486_);
return v___x_1489_;
}
else
{
lean_object* v_val_1490_; 
v_val_1490_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_val_1490_);
lean_dec_ref_known(v___x_1488_, 1);
if (lean_obj_tag(v_val_1490_) == 1)
{
uint8_t v_v_1491_; 
v_v_1491_ = lean_ctor_get_uint8(v_val_1490_, 0);
lean_dec_ref_known(v_val_1490_, 0);
return v_v_1491_;
}
else
{
uint8_t v___x_1492_; 
lean_dec(v_val_1490_);
v___x_1492_ = lean_unbox(v_defValue_1486_);
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1493_, lean_object* v_opt_1494_){
_start:
{
uint8_t v_res_1495_; lean_object* v_r_1496_; 
v_res_1495_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1493_, v_opt_1494_);
lean_dec_ref(v_opt_1494_);
lean_dec_ref(v_opts_1493_);
v_r_1496_ = lean_box(v_res_1495_);
return v_r_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1497_, lean_object* v_fnIndex_1498_, lean_object* v_recArg_1499_, lean_object* v_below_1500_, lean_object* v_Cs_1501_, lean_object* v_belowDict_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_array_get_borrowed(v___x_1497_, v_Cs_1501_, v_fnIndex_1498_);
lean_inc(v___x_1508_);
v___x_1509_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1508_, v_belowDict_1502_, v_recArg_1499_, v_below_1500_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1510_, lean_object* v_fnIndex_1511_, lean_object* v_recArg_1512_, lean_object* v_below_1513_, lean_object* v_Cs_1514_, lean_object* v_belowDict_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1510_, v_fnIndex_1511_, v_recArg_1512_, v_below_1513_, v_Cs_1514_, v_belowDict_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_Cs_1514_);
lean_dec(v_fnIndex_1511_);
lean_dec_ref(v___x_1510_);
return v_res_1521_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1528_, lean_object* v_recArg_1529_, lean_object* v_x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
lean_inc(v___y_1534_);
lean_inc_ref(v___y_1533_);
lean_inc(v___y_1532_);
lean_inc_ref(v___y_1531_);
v___x_1536_ = lean_infer_type(v_below_1528_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1551_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1541_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1542_ = l_Lean_MessageData_ofExpr(v_recArg_1529_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_MessageData_ofExpr(v_a_1537_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1547_);
v___x_1549_ = v___x_1539_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v_recArg_1529_);
v_a_1552_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1536_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1536_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1560_, lean_object* v_recArg_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1560_, v_recArg_1561_, v_x_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v_x_1562_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t v_sz_1569_, size_t v_i_1570_, lean_object* v_bs_1571_){
_start:
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_usize_dec_lt(v_i_1570_, v_sz_1569_);
if (v___x_1572_ == 0)
{
return v_bs_1571_;
}
else
{
lean_object* v_v_1573_; lean_object* v_msg_1574_; lean_object* v___x_1575_; lean_object* v_bs_x27_1576_; size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v_v_1573_ = lean_array_uget_borrowed(v_bs_1571_, v_i_1570_);
v_msg_1574_ = lean_ctor_get(v_v_1573_, 1);
lean_inc_ref(v_msg_1574_);
v___x_1575_ = lean_unsigned_to_nat(0u);
v_bs_x27_1576_ = lean_array_uset(v_bs_1571_, v_i_1570_, v___x_1575_);
v___x_1577_ = ((size_t)1ULL);
v___x_1578_ = lean_usize_add(v_i_1570_, v___x_1577_);
v___x_1579_ = lean_array_uset(v_bs_x27_1576_, v_i_1570_, v_msg_1574_);
v_i_1570_ = v___x_1578_;
v_bs_1571_ = v___x_1579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1581_, lean_object* v_i_1582_, lean_object* v_bs_1583_){
_start:
{
size_t v_sz_boxed_1584_; size_t v_i_boxed_1585_; lean_object* v_res_1586_; 
v_sz_boxed_1584_ = lean_unbox_usize(v_sz_1581_);
lean_dec(v_sz_1581_);
v_i_boxed_1585_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_res_1586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_boxed_1584_, v_i_boxed_1585_, v_bs_1583_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_oldTraces_1587_, lean_object* v_data_1588_, lean_object* v_ref_1589_, lean_object* v_msg_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_toCold_1596_; lean_object* v_currRecDepth_1597_; lean_object* v_ref_1598_; uint8_t v_diag_1599_; uint8_t v_suppressElabErrors_1600_; lean_object* v_ref_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v_traceState_1604_; lean_object* v_traces_1605_; lean_object* v___x_1606_; size_t v_sz_1607_; size_t v___x_1608_; lean_object* v___x_1609_; lean_object* v_msg_1610_; lean_object* v___x_1611_; lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1649_; 
v_toCold_1596_ = lean_ctor_get(v___y_1593_, 0);
v_currRecDepth_1597_ = lean_ctor_get(v___y_1593_, 1);
v_ref_1598_ = lean_ctor_get(v___y_1593_, 2);
v_diag_1599_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*3);
v_suppressElabErrors_1600_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*3 + 1);
v_ref_1601_ = l_Lean_replaceRef(v_ref_1589_, v_ref_1598_);
lean_inc(v_currRecDepth_1597_);
lean_inc_ref(v_toCold_1596_);
v___x_1602_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1602_, 0, v_toCold_1596_);
lean_ctor_set(v___x_1602_, 1, v_currRecDepth_1597_);
lean_ctor_set(v___x_1602_, 2, v_ref_1601_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3, v_diag_1599_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 1, v_suppressElabErrors_1600_);
v___x_1603_ = lean_st_ref_get(v___y_1594_);
v_traceState_1604_ = lean_ctor_get(v___x_1603_, 4);
lean_inc_ref(v_traceState_1604_);
lean_dec(v___x_1603_);
v_traces_1605_ = lean_ctor_get(v_traceState_1604_, 0);
lean_inc_ref(v_traces_1605_);
lean_dec_ref(v_traceState_1604_);
v___x_1606_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1605_);
lean_dec_ref(v_traces_1605_);
v_sz_1607_ = lean_array_size(v___x_1606_);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1607_, v___x_1608_, v___x_1606_);
v_msg_1610_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1610_, 0, v_data_1588_);
lean_ctor_set(v_msg_1610_, 1, v_msg_1590_);
lean_ctor_set(v_msg_1610_, 2, v___x_1609_);
v___x_1611_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1610_, v___y_1591_, v___y_1592_, v___x_1602_, v___y_1594_);
lean_dec_ref_known(v___x_1602_, 3);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1649_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1649_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v_traceState_1617_; lean_object* v_env_1618_; lean_object* v_nextMacroScope_1619_; lean_object* v_ngen_1620_; lean_object* v_auxDeclNGen_1621_; lean_object* v_cache_1622_; lean_object* v_messages_1623_; lean_object* v_infoState_1624_; lean_object* v_snapshotTasks_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1648_; 
v___x_1616_ = lean_st_ref_take(v___y_1594_);
v_traceState_1617_ = lean_ctor_get(v___x_1616_, 4);
v_env_1618_ = lean_ctor_get(v___x_1616_, 0);
v_nextMacroScope_1619_ = lean_ctor_get(v___x_1616_, 1);
v_ngen_1620_ = lean_ctor_get(v___x_1616_, 2);
v_auxDeclNGen_1621_ = lean_ctor_get(v___x_1616_, 3);
v_cache_1622_ = lean_ctor_get(v___x_1616_, 5);
v_messages_1623_ = lean_ctor_get(v___x_1616_, 6);
v_infoState_1624_ = lean_ctor_get(v___x_1616_, 7);
v_snapshotTasks_1625_ = lean_ctor_get(v___x_1616_, 8);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1627_ = v___x_1616_;
v_isShared_1628_ = v_isSharedCheck_1648_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_snapshotTasks_1625_);
lean_inc(v_infoState_1624_);
lean_inc(v_messages_1623_);
lean_inc(v_cache_1622_);
lean_inc(v_traceState_1617_);
lean_inc(v_auxDeclNGen_1621_);
lean_inc(v_ngen_1620_);
lean_inc(v_nextMacroScope_1619_);
lean_inc(v_env_1618_);
lean_dec(v___x_1616_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1648_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
uint64_t v_tid_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1646_; 
v_tid_1629_ = lean_ctor_get_uint64(v_traceState_1617_, sizeof(void*)*1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_traceState_1617_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v_traceState_1617_, 0);
lean_dec(v_unused_1647_);
v___x_1631_ = v_traceState_1617_;
v_isShared_1632_ = v_isSharedCheck_1646_;
goto v_resetjp_1630_;
}
else
{
lean_dec(v_traceState_1617_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1646_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_ref_1589_);
lean_ctor_set(v___x_1634_, 1, v_a_1612_);
v___x_1635_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1587_, v___x_1634_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1635_);
v___x_1637_ = v___x_1631_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1635_);
lean_ctor_set_uint64(v_reuseFailAlloc_1645_, sizeof(void*)*1, v_tid_1629_);
v___x_1637_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 4, v___x_1637_);
v___x_1639_ = v___x_1627_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_env_1618_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_nextMacroScope_1619_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_ngen_1620_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_auxDeclNGen_1621_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v_cache_1622_);
lean_ctor_set(v_reuseFailAlloc_1644_, 6, v_messages_1623_);
lean_ctor_set(v_reuseFailAlloc_1644_, 7, v_infoState_1624_);
lean_ctor_set(v_reuseFailAlloc_1644_, 8, v_snapshotTasks_1625_);
v___x_1639_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_st_ref_put(v___y_1594_, v___x_1639_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1633_);
v___x_1642_ = v___x_1614_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1633_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1650_, lean_object* v_data_1651_, lean_object* v_ref_1652_, lean_object* v_msg_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1650_, v_data_1651_, v_ref_1652_, v_msg_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1660_, lean_object* v_opt_1661_){
_start:
{
lean_object* v_name_1662_; lean_object* v_defValue_1663_; lean_object* v_map_1664_; lean_object* v___x_1665_; 
v_name_1662_ = lean_ctor_get(v_opt_1661_, 0);
v_defValue_1663_ = lean_ctor_get(v_opt_1661_, 1);
v_map_1664_ = lean_ctor_get(v_opts_1660_, 0);
v___x_1665_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1664_, v_name_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_inc(v_defValue_1663_);
return v_defValue_1663_;
}
else
{
lean_object* v_val_1666_; 
v_val_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v___x_1665_, 1);
if (lean_obj_tag(v_val_1666_) == 3)
{
lean_object* v_v_1667_; 
v_v_1667_ = lean_ctor_get(v_val_1666_, 0);
lean_inc(v_v_1667_);
lean_dec_ref_known(v_val_1666_, 1);
return v_v_1667_;
}
else
{
lean_dec(v_val_1666_);
lean_inc(v_defValue_1663_);
return v_defValue_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1668_, lean_object* v_opt_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1668_, v_opt_1669_);
lean_dec_ref(v_opt_1669_);
lean_dec_ref(v_opts_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1671_){
_start:
{
if (lean_obj_tag(v_e_1671_) == 0)
{
uint8_t v___x_1672_; 
v___x_1672_ = 2;
return v___x_1672_;
}
else
{
lean_object* v_a_1673_; uint8_t v___x_1674_; 
v_a_1673_ = lean_ctor_get(v_e_1671_, 0);
v___x_1674_ = l_Lean_Expr_hasSyntheticSorry(v_a_1673_);
if (v___x_1674_ == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = 0;
return v___x_1675_;
}
else
{
uint8_t v___x_1676_; 
v___x_1676_ = 1;
return v___x_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1677_){
_start:
{
uint8_t v_res_1678_; lean_object* v_r_1679_; 
v_res_1678_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1677_);
lean_dec_ref(v_e_1677_);
v_r_1679_ = lean_box(v_res_1678_);
return v_r_1679_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object* v_x_1680_){
_start:
{
if (lean_obj_tag(v_x_1680_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v_x_1680_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_x_1680_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v_x_1680_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v_x_1680_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 1);
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v_x_1680_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_x_1680_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v_x_1680_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v_x_1680_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 0);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1698_);
return v_res_1700_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
return v___x_1703_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1704_; double v___x_1705_; 
v___x_1704_ = lean_unsigned_to_nat(1000u);
v___x_1705_ = lean_float_of_nat(v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1706_, uint8_t v_collapsed_1707_, lean_object* v_tag_1708_, lean_object* v_opts_1709_, uint8_t v_clsEnabled_1710_, lean_object* v_oldTraces_1711_, lean_object* v_msg_1712_, lean_object* v_resStartStop_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_fst_1719_; lean_object* v_snd_1720_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v_data_1724_; lean_object* v_fst_1735_; lean_object* v_snd_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; lean_object* v___y_1740_; lean_object* v_a_1741_; uint8_t v___y_1756_; double v___y_1787_; 
v_fst_1719_ = lean_ctor_get(v_resStartStop_1713_, 0);
lean_inc(v_fst_1719_);
v_snd_1720_ = lean_ctor_get(v_resStartStop_1713_, 1);
lean_inc(v_snd_1720_);
lean_dec_ref(v_resStartStop_1713_);
v_fst_1735_ = lean_ctor_get(v_snd_1720_, 0);
lean_inc(v_fst_1735_);
v_snd_1736_ = lean_ctor_get(v_snd_1720_, 1);
lean_inc(v_snd_1736_);
lean_dec(v_snd_1720_);
v___x_1737_ = l_Lean_trace_profiler;
v___x_1738_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1709_, v___x_1737_);
if (v___x_1738_ == 0)
{
v___y_1756_ = v___x_1738_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1793_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1709_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; double v___x_1796_; double v___x_1797_; double v___x_1798_; 
v___x_1794_ = l_Lean_trace_profiler_threshold;
v___x_1795_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1709_, v___x_1794_);
v___x_1796_ = lean_float_of_nat(v___x_1795_);
v___x_1797_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2);
v___x_1798_ = lean_float_div(v___x_1796_, v___x_1797_);
v___y_1787_ = v___x_1798_;
goto v___jp_1786_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; double v___x_1801_; 
v___x_1799_ = l_Lean_trace_profiler_threshold;
v___x_1800_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1709_, v___x_1799_);
v___x_1801_ = lean_float_of_nat(v___x_1800_);
v___y_1787_ = v___x_1801_;
goto v___jp_1786_;
}
}
v___jp_1721_:
{
lean_object* v___x_1725_; 
lean_inc(v___y_1723_);
v___x_1725_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1711_, v_data_1724_, v___y_1723_, v___y_1722_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v___x_1726_; 
lean_dec_ref_known(v___x_1725_, 1);
v___x_1726_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1719_);
return v___x_1726_;
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_fst_1719_);
v_a_1727_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1725_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
v___jp_1739_:
{
uint8_t v_result_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; double v___x_1745_; lean_object* v_data_1746_; 
v_result_1742_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1719_);
v___x_1743_ = lean_box(v_result_1742_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
v___x_1745_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1708_);
lean_inc_ref(v___x_1744_);
lean_inc(v_cls_1706_);
v_data_1746_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1746_, 0, v_cls_1706_);
lean_ctor_set(v_data_1746_, 1, v___x_1744_);
lean_ctor_set(v_data_1746_, 2, v_tag_1708_);
lean_ctor_set_float(v_data_1746_, sizeof(void*)*3, v___x_1745_);
lean_ctor_set_float(v_data_1746_, sizeof(void*)*3 + 8, v___x_1745_);
lean_ctor_set_uint8(v_data_1746_, sizeof(void*)*3 + 16, v_collapsed_1707_);
if (v___x_1738_ == 0)
{
lean_dec_ref_known(v___x_1744_, 1);
lean_dec(v_snd_1736_);
lean_dec(v_fst_1735_);
lean_dec_ref(v_tag_1708_);
lean_dec(v_cls_1706_);
v___y_1722_ = v_a_1741_;
v___y_1723_ = v___y_1740_;
v_data_1724_ = v_data_1746_;
goto v___jp_1721_;
}
else
{
lean_object* v_data_1747_; double v___x_1748_; double v___x_1749_; 
lean_dec_ref_known(v_data_1746_, 3);
v_data_1747_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1747_, 0, v_cls_1706_);
lean_ctor_set(v_data_1747_, 1, v___x_1744_);
lean_ctor_set(v_data_1747_, 2, v_tag_1708_);
v___x_1748_ = lean_unbox_float(v_fst_1735_);
lean_dec(v_fst_1735_);
lean_ctor_set_float(v_data_1747_, sizeof(void*)*3, v___x_1748_);
v___x_1749_ = lean_unbox_float(v_snd_1736_);
lean_dec(v_snd_1736_);
lean_ctor_set_float(v_data_1747_, sizeof(void*)*3 + 8, v___x_1749_);
lean_ctor_set_uint8(v_data_1747_, sizeof(void*)*3 + 16, v_collapsed_1707_);
v___y_1722_ = v_a_1741_;
v___y_1723_ = v___y_1740_;
v_data_1724_ = v_data_1747_;
goto v___jp_1721_;
}
}
v___jp_1750_:
{
lean_object* v_ref_1751_; lean_object* v___x_1752_; 
v_ref_1751_ = lean_ctor_get(v___y_1716_, 2);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
lean_inc(v___y_1715_);
lean_inc_ref(v___y_1714_);
lean_inc(v_fst_1719_);
v___x_1752_ = lean_apply_6(v_msg_1712_, v_fst_1719_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, lean_box(0));
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___y_1740_ = v_ref_1751_;
v_a_1741_ = v_a_1753_;
goto v___jp_1739_;
}
else
{
lean_object* v___x_1754_; 
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
v___y_1740_ = v_ref_1751_;
v_a_1741_ = v___x_1754_;
goto v___jp_1739_;
}
}
v___jp_1755_:
{
if (v_clsEnabled_1710_ == 0)
{
if (v___y_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v_traceState_1758_; lean_object* v_env_1759_; lean_object* v_nextMacroScope_1760_; lean_object* v_ngen_1761_; lean_object* v_auxDeclNGen_1762_; lean_object* v_cache_1763_; lean_object* v_messages_1764_; lean_object* v_infoState_1765_; lean_object* v_snapshotTasks_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_snd_1736_);
lean_dec(v_fst_1735_);
lean_dec_ref(v_msg_1712_);
lean_dec_ref(v_tag_1708_);
lean_dec(v_cls_1706_);
v___x_1757_ = lean_st_ref_take(v___y_1717_);
v_traceState_1758_ = lean_ctor_get(v___x_1757_, 4);
v_env_1759_ = lean_ctor_get(v___x_1757_, 0);
v_nextMacroScope_1760_ = lean_ctor_get(v___x_1757_, 1);
v_ngen_1761_ = lean_ctor_get(v___x_1757_, 2);
v_auxDeclNGen_1762_ = lean_ctor_get(v___x_1757_, 3);
v_cache_1763_ = lean_ctor_get(v___x_1757_, 5);
v_messages_1764_ = lean_ctor_get(v___x_1757_, 6);
v_infoState_1765_ = lean_ctor_get(v___x_1757_, 7);
v_snapshotTasks_1766_ = lean_ctor_get(v___x_1757_, 8);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1768_ = v___x_1757_;
v_isShared_1769_ = v_isSharedCheck_1785_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_snapshotTasks_1766_);
lean_inc(v_infoState_1765_);
lean_inc(v_messages_1764_);
lean_inc(v_cache_1763_);
lean_inc(v_traceState_1758_);
lean_inc(v_auxDeclNGen_1762_);
lean_inc(v_ngen_1761_);
lean_inc(v_nextMacroScope_1760_);
lean_inc(v_env_1759_);
lean_dec(v___x_1757_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1785_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
uint64_t v_tid_1770_; lean_object* v_traces_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1784_; 
v_tid_1770_ = lean_ctor_get_uint64(v_traceState_1758_, sizeof(void*)*1);
v_traces_1771_ = lean_ctor_get(v_traceState_1758_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_traceState_1758_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1773_ = v_traceState_1758_;
v_isShared_1774_ = v_isSharedCheck_1784_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_traces_1771_);
lean_dec(v_traceState_1758_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1784_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1711_, v_traces_1771_);
lean_dec_ref(v_traces_1771_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1775_);
lean_ctor_set_uint64(v_reuseFailAlloc_1783_, sizeof(void*)*1, v_tid_1770_);
v___x_1777_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1779_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 4, v___x_1777_);
v___x_1779_ = v___x_1768_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_env_1759_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_nextMacroScope_1760_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_ngen_1761_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_auxDeclNGen_1762_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1782_, 5, v_cache_1763_);
lean_ctor_set(v_reuseFailAlloc_1782_, 6, v_messages_1764_);
lean_ctor_set(v_reuseFailAlloc_1782_, 7, v_infoState_1765_);
lean_ctor_set(v_reuseFailAlloc_1782_, 8, v_snapshotTasks_1766_);
v___x_1779_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_st_ref_put(v___y_1717_, v___x_1779_);
v___x_1781_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1719_);
return v___x_1781_;
}
}
}
}
}
else
{
goto v___jp_1750_;
}
}
else
{
goto v___jp_1750_;
}
}
v___jp_1786_:
{
double v___x_1788_; double v___x_1789_; double v___x_1790_; uint8_t v___x_1791_; 
v___x_1788_ = lean_unbox_float(v_snd_1736_);
v___x_1789_ = lean_unbox_float(v_fst_1735_);
v___x_1790_ = lean_float_sub(v___x_1788_, v___x_1789_);
v___x_1791_ = lean_float_decLt(v___y_1787_, v___x_1790_);
v___y_1756_ = v___x_1791_;
goto v___jp_1755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1802_, lean_object* v_collapsed_1803_, lean_object* v_tag_1804_, lean_object* v_opts_1805_, lean_object* v_clsEnabled_1806_, lean_object* v_oldTraces_1807_, lean_object* v_msg_1808_, lean_object* v_resStartStop_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
uint8_t v_collapsed_boxed_1815_; uint8_t v_clsEnabled_boxed_1816_; lean_object* v_res_1817_; 
v_collapsed_boxed_1815_ = lean_unbox(v_collapsed_1803_);
v_clsEnabled_boxed_1816_ = lean_unbox(v_clsEnabled_1806_);
v_res_1817_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1802_, v_collapsed_boxed_1815_, v_tag_1804_, v_opts_1805_, v_clsEnabled_boxed_1816_, v_oldTraces_1807_, v_msg_1808_, v_resStartStop_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec_ref(v_opts_1805_);
return v_res_1817_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1819_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1820_ = l_Lean_Name_append(v___x_1819_, v___x_1818_);
return v___x_1820_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__1(void){
_start:
{
lean_object* v___x_1821_; double v___x_1822_; 
v___x_1821_ = lean_unsigned_to_nat(1000000000u);
v___x_1822_ = lean_float_of_nat(v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1823_, lean_object* v_numIndParams_1824_, lean_object* v_positions_1825_, lean_object* v_fnIndex_1826_, lean_object* v_recArg_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_toCold_1833_; lean_object* v_options_1834_; lean_object* v_inheritedTraceOptions_1835_; uint8_t v_hasTrace_1836_; lean_object* v___x_1837_; lean_object* v___f_1838_; 
v_toCold_1833_ = lean_ctor_get(v_a_1830_, 0);
v_options_1834_ = lean_ctor_get(v_toCold_1833_, 2);
v_inheritedTraceOptions_1835_ = lean_ctor_get(v_toCold_1833_, 11);
v_hasTrace_1836_ = lean_ctor_get_uint8(v_options_1834_, sizeof(void*)*1);
v___x_1837_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1823_);
lean_inc_ref(v_recArg_1827_);
v___f_1838_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1838_, 0, v___x_1837_);
lean_closure_set(v___f_1838_, 1, v_fnIndex_1826_);
lean_closure_set(v___f_1838_, 2, v_recArg_1827_);
lean_closure_set(v___f_1838_, 3, v_below_1823_);
if (v_hasTrace_1836_ == 0)
{
lean_object* v___x_1839_; 
lean_dec_ref(v_recArg_1827_);
v___x_1839_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1823_, v_numIndParams_1824_, v_positions_1825_, v___f_1838_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
return v___x_1839_;
}
else
{
lean_object* v___f_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v_a_1848_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v_a_1863_; 
lean_inc_ref(v_below_1823_);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1840_, 0, v_below_1823_);
lean_closure_set(v___f_1840_, 1, v_recArg_1827_);
v___x_1841_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1842_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1843_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1844_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1835_, v_options_1834_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1913_ = l_Lean_trace_profiler;
v___x_1914_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1834_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref(v___f_1840_);
v___x_1915_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1823_, v_numIndParams_1824_, v_positions_1825_, v___f_1838_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
return v___x_1915_;
}
else
{
goto v___jp_1872_;
}
}
else
{
goto v___jp_1872_;
}
v___jp_1845_:
{
lean_object* v___x_1849_; double v___x_1850_; double v___x_1851_; double v___x_1852_; double v___x_1853_; double v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1849_ = lean_io_mono_nanos_now();
v___x_1850_ = lean_float_of_nat(v___y_1846_);
v___x_1851_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__1, &l_Lean_Elab_Structural_toBelow___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___closed__1);
v___x_1852_ = lean_float_div(v___x_1850_, v___x_1851_);
v___x_1853_ = lean_float_of_nat(v___x_1849_);
v___x_1854_ = lean_float_div(v___x_1853_, v___x_1851_);
v___x_1855_ = lean_box_float(v___x_1852_);
v___x_1856_ = lean_box_float(v___x_1854_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_a_1848_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1841_, v_hasTrace_1836_, v___x_1842_, v_options_1834_, v___x_1844_, v___y_1847_, v___f_1840_, v___x_1858_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
return v___x_1859_;
}
v___jp_1860_:
{
lean_object* v___x_1864_; double v___x_1865_; double v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1864_ = lean_io_get_num_heartbeats();
v___x_1865_ = lean_float_of_nat(v___y_1861_);
v___x_1866_ = lean_float_of_nat(v___x_1864_);
v___x_1867_ = lean_box_float(v___x_1865_);
v___x_1868_ = lean_box_float(v___x_1866_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_a_1863_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1841_, v_hasTrace_1836_, v___x_1842_, v_options_1834_, v___x_1844_, v___y_1862_, v___f_1840_, v___x_1870_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
return v___x_1871_;
}
v___jp_1872_:
{
lean_object* v___x_1873_; lean_object* v_a_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1873_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1831_);
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1876_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1834_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_io_mono_nanos_now();
v___x_1878_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1823_, v_numIndParams_1824_, v_positions_1825_, v___f_1838_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 1);
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
v___y_1846_ = v___x_1877_;
v___y_1847_ = v_a_1874_;
v_a_1848_ = v___x_1884_;
goto v___jp_1845_;
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
v_a_1887_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1878_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1878_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 0);
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
v___y_1846_ = v___x_1877_;
v___y_1847_ = v_a_1874_;
v_a_1848_ = v___x_1892_;
goto v___jp_1845_;
}
}
}
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_io_get_num_heartbeats();
v___x_1896_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1823_, v_numIndParams_1824_, v_positions_1825_, v___f_1838_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 1);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
v___y_1861_ = v___x_1895_;
v___y_1862_ = v_a_1874_;
v_a_1863_ = v___x_1902_;
goto v___jp_1860_;
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_a_1905_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1896_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1896_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 0);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
v___y_1861_ = v___x_1895_;
v___y_1862_ = v_a_1874_;
v_a_1863_ = v___x_1910_;
goto v___jp_1860_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1916_, lean_object* v_numIndParams_1917_, lean_object* v_positions_1918_, lean_object* v_fnIndex_1919_, lean_object* v_recArg_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Elab_Structural_toBelow(v_below_1916_, v_numIndParams_1917_, v_positions_1918_, v_fnIndex_1919_, v_recArg_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1928_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1935_, lean_object* v_x_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1935_, v_x_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1943_, lean_object* v___y_1944_, lean_object* v_b_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
lean_inc(v___y_1949_);
lean_inc_ref(v___y_1948_);
lean_inc(v___y_1947_);
lean_inc_ref(v___y_1946_);
lean_inc(v___y_1944_);
v___x_1951_ = lean_apply_7(v_k_1943_, v_b_1945_, v___y_1944_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, lean_box(0));
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_1952_, lean_object* v___y_1953_, lean_object* v_b_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_1952_, v___y_1953_, v_b_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1953_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_1961_, uint8_t v_bi_1962_, lean_object* v_type_1963_, lean_object* v_k_1964_, uint8_t v_kind_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___f_1972_; lean_object* v___x_1973_; 
lean_inc(v___y_1966_);
v___f_1972_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1972_, 0, v_k_1964_);
lean_closure_set(v___f_1972_, 1, v___y_1966_);
v___x_1973_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1961_, v_bi_1962_, v_type_1963_, v___f_1972_, v_kind_1965_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
if (lean_obj_tag(v___x_1973_) == 0)
{
return v___x_1973_;
}
else
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
return v___x_1979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_1982_, lean_object* v_bi_1983_, lean_object* v_type_1984_, lean_object* v_k_1985_, lean_object* v_kind_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v_bi_boxed_1993_; uint8_t v_kind_boxed_1994_; lean_object* v_res_1995_; 
v_bi_boxed_1993_ = lean_unbox(v_bi_1983_);
v_kind_boxed_1994_ = lean_unbox(v_kind_1986_);
v_res_1995_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_1982_, v_bi_boxed_1993_, v_type_1984_, v_k_1985_, v_kind_boxed_1994_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_1996_, lean_object* v_name_1997_, uint8_t v_bi_1998_, lean_object* v_type_1999_, lean_object* v_k_2000_, uint8_t v_kind_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_1997_, v_bi_1998_, v_type_1999_, v_k_2000_, v_kind_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2009_, lean_object* v_name_2010_, lean_object* v_bi_2011_, lean_object* v_type_2012_, lean_object* v_k_2013_, lean_object* v_kind_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v_bi_boxed_2021_; uint8_t v_kind_boxed_2022_; lean_object* v_res_2023_; 
v_bi_boxed_2021_ = lean_unbox(v_bi_2011_);
v_kind_boxed_2022_ = lean_unbox(v_kind_2014_);
v_res_2023_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2009_, v_name_2010_, v_bi_boxed_2021_, v_type_2012_, v_k_2013_, v_kind_boxed_2022_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2024_, lean_object* v___y_2025_, lean_object* v_b_2026_, lean_object* v_c_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v___x_2033_; 
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2030_);
lean_inc(v___y_2029_);
lean_inc_ref(v___y_2028_);
lean_inc(v___y_2025_);
v___x_2033_ = lean_apply_8(v_k_2024_, v_b_2026_, v_c_2027_, v___y_2025_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, lean_box(0));
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2034_, lean_object* v___y_2035_, lean_object* v_b_2036_, lean_object* v_c_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2034_, v___y_2035_, v_b_2036_, v_c_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2035_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2044_, lean_object* v_maxFVars_2045_, lean_object* v_k_2046_, uint8_t v_cleanupAnnotations_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___f_2054_; uint8_t v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_inc(v___y_2048_);
v___f_2054_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2054_, 0, v_k_2046_);
lean_closure_set(v___f_2054_, 1, v___y_2048_);
v___x_2055_ = 1;
v___x_2056_ = 0;
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_maxFVars_2045_);
v___x_2058_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2044_, v___x_2055_, v___x_2056_, v___x_2055_, v___x_2056_, v___x_2057_, v___f_2054_, v_cleanupAnnotations_2047_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec_ref_known(v___x_2057_, 1);
if (lean_obj_tag(v___x_2058_) == 0)
{
return v___x_2058_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2067_, lean_object* v_maxFVars_2068_, lean_object* v_k_2069_, lean_object* v_cleanupAnnotations_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2077_; lean_object* v_res_2078_; 
v_cleanupAnnotations_boxed_2077_ = lean_unbox(v_cleanupAnnotations_2070_);
v_res_2078_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2067_, v_maxFVars_2068_, v_k_2069_, v_cleanupAnnotations_boxed_2077_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2079_, lean_object* v_e_2080_, lean_object* v_maxFVars_2081_, lean_object* v_k_2082_, uint8_t v_cleanupAnnotations_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2080_, v_maxFVars_2081_, v_k_2082_, v_cleanupAnnotations_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2091_, lean_object* v_e_2092_, lean_object* v_maxFVars_2093_, lean_object* v_k_2094_, lean_object* v_cleanupAnnotations_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2102_; lean_object* v_res_2103_; 
v_cleanupAnnotations_boxed_2102_ = lean_unbox(v_cleanupAnnotations_2095_);
v_res_2103_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2091_, v_e_2092_, v_maxFVars_2093_, v_k_2094_, v_cleanupAnnotations_boxed_2102_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2104_, lean_object* v_msg_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_ref_2111_; lean_object* v___x_2112_; lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2157_; 
v_ref_2111_ = lean_ctor_get(v___y_2108_, 2);
v___x_2112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2157_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2157_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v_traceState_2118_; lean_object* v_env_2119_; lean_object* v_nextMacroScope_2120_; lean_object* v_ngen_2121_; lean_object* v_auxDeclNGen_2122_; lean_object* v_cache_2123_; lean_object* v_messages_2124_; lean_object* v_infoState_2125_; lean_object* v_snapshotTasks_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2156_; 
v___x_2117_ = lean_st_ref_take(v___y_2109_);
v_traceState_2118_ = lean_ctor_get(v___x_2117_, 4);
v_env_2119_ = lean_ctor_get(v___x_2117_, 0);
v_nextMacroScope_2120_ = lean_ctor_get(v___x_2117_, 1);
v_ngen_2121_ = lean_ctor_get(v___x_2117_, 2);
v_auxDeclNGen_2122_ = lean_ctor_get(v___x_2117_, 3);
v_cache_2123_ = lean_ctor_get(v___x_2117_, 5);
v_messages_2124_ = lean_ctor_get(v___x_2117_, 6);
v_infoState_2125_ = lean_ctor_get(v___x_2117_, 7);
v_snapshotTasks_2126_ = lean_ctor_get(v___x_2117_, 8);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2128_ = v___x_2117_;
v_isShared_2129_ = v_isSharedCheck_2156_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snapshotTasks_2126_);
lean_inc(v_infoState_2125_);
lean_inc(v_messages_2124_);
lean_inc(v_cache_2123_);
lean_inc(v_traceState_2118_);
lean_inc(v_auxDeclNGen_2122_);
lean_inc(v_ngen_2121_);
lean_inc(v_nextMacroScope_2120_);
lean_inc(v_env_2119_);
lean_dec(v___x_2117_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2156_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
uint64_t v_tid_2130_; lean_object* v_traces_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2155_; 
v_tid_2130_ = lean_ctor_get_uint64(v_traceState_2118_, sizeof(void*)*1);
v_traces_2131_ = lean_ctor_get(v_traceState_2118_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_traceState_2118_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2133_ = v_traceState_2118_;
v_isShared_2134_ = v_isSharedCheck_2155_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_traces_2131_);
lean_dec(v_traceState_2118_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2155_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; double v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2135_ = lean_box(0);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2138_ = 0;
v___x_2139_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2140_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2140_, 0, v_cls_2104_);
lean_ctor_set(v___x_2140_, 1, v___x_2136_);
lean_ctor_set(v___x_2140_, 2, v___x_2139_);
lean_ctor_set_float(v___x_2140_, sizeof(void*)*3, v___x_2137_);
lean_ctor_set_float(v___x_2140_, sizeof(void*)*3 + 8, v___x_2137_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*3 + 16, v___x_2138_);
v___x_2141_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2142_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v_a_2113_);
lean_ctor_set(v___x_2142_, 2, v___x_2141_);
lean_inc(v_ref_2111_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v_ref_2111_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_PersistentArray_push___redArg(v_traces_2131_, v___x_2143_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2144_);
v___x_2146_ = v___x_2133_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2144_);
lean_ctor_set_uint64(v_reuseFailAlloc_2154_, sizeof(void*)*1, v_tid_2130_);
v___x_2146_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 4, v___x_2146_);
v___x_2148_ = v___x_2128_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_env_2119_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_nextMacroScope_2120_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_ngen_2121_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_auxDeclNGen_2122_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 5, v_cache_2123_);
lean_ctor_set(v_reuseFailAlloc_2153_, 6, v_messages_2124_);
lean_ctor_set(v_reuseFailAlloc_2153_, 7, v_infoState_2125_);
lean_ctor_set(v_reuseFailAlloc_2153_, 8, v_snapshotTasks_2126_);
v___x_2148_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_st_ref_put(v___y_2109_, v___x_2148_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2135_);
v___x_2151_ = v___x_2115_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2135_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2158_, lean_object* v_msg_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2158_, v_msg_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
return v_res_2165_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2166_, lean_object* v_as_2167_, size_t v_i_2168_, size_t v_stop_2169_){
_start:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_usize_dec_eq(v_i_2168_, v_stop_2169_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v_fnName_2176_; lean_object* v_recArgPos_2177_; uint8_t v___x_2178_; 
v___x_2175_ = lean_array_uget_borrowed(v_as_2167_, v_i_2168_);
v_fnName_2176_ = lean_ctor_get(v___x_2175_, 0);
v_recArgPos_2177_ = lean_ctor_get(v___x_2175_, 2);
lean_inc(v_recArgPos_2177_);
lean_inc(v_fnName_2176_);
v___x_2178_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2176_, v_recArgPos_2177_, v_e_2166_);
if (v___x_2178_ == 0)
{
goto v___jp_2170_;
}
else
{
if (v___x_2178_ == 0)
{
goto v___jp_2170_;
}
else
{
return v___x_2178_;
}
}
}
else
{
uint8_t v___x_2179_; 
v___x_2179_ = 0;
return v___x_2179_;
}
v___jp_2170_:
{
size_t v___x_2171_; size_t v___x_2172_; 
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_add(v_i_2168_, v___x_2171_);
v_i_2168_ = v___x_2172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2180_, lean_object* v_as_2181_, lean_object* v_i_2182_, lean_object* v_stop_2183_){
_start:
{
size_t v_i_boxed_2184_; size_t v_stop_boxed_2185_; uint8_t v_res_2186_; lean_object* v_r_2187_; 
v_i_boxed_2184_ = lean_unbox_usize(v_i_2182_);
lean_dec(v_i_2182_);
v_stop_boxed_2185_ = lean_unbox_usize(v_stop_2183_);
lean_dec(v_stop_2183_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2180_, v_as_2181_, v_i_boxed_2184_, v_stop_boxed_2185_);
lean_dec_ref(v_as_2181_);
lean_dec_ref(v_e_2180_);
v_r_2187_ = lean_box(v_res_2186_);
return v_r_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2188_, lean_object* v_____do__lift_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_toCold_2196_; lean_object* v_options_2197_; uint8_t v_hasTrace_2198_; 
v_toCold_2196_ = lean_ctor_get(v___y_2193_, 0);
v_options_2197_ = lean_ctor_get(v_toCold_2196_, 2);
v_hasTrace_2198_ = lean_ctor_get_uint8(v_options_2197_, sizeof(void*)*1);
if (v_hasTrace_2198_ == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v___x_2188_);
v___x_2199_ = lean_box(v_hasTrace_2198_);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2202_ = l_Lean_Name_append(v___x_2201_, v___x_2188_);
v___x_2203_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2189_, v_options_2197_, v___x_2202_);
lean_dec(v___x_2202_);
v___x_2204_ = lean_box(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2206_, lean_object* v_____do__lift_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2206_, v_____do__lift_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v_____do__lift_2207_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v_env_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2218_ = lean_st_ref_get(v___y_2216_);
v_env_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_ref(v_env_2219_);
lean_dec(v___x_2218_);
v___x_2220_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2219_, v_declName_2215_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2222_, v___y_2223_);
lean_dec(v___y_2223_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v_toApplicative_2234_; lean_object* v_toFunctor_2235_; lean_object* v_toSeq_2236_; lean_object* v_toSeqLeft_2237_; lean_object* v_toSeqRight_2238_; lean_object* v___f_2239_; lean_object* v___f_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___x_2243_; lean_object* v___f_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_toApplicative_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2282_; 
v___x_2233_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2234_ = lean_ctor_get(v___x_2233_, 0);
v_toFunctor_2235_ = lean_ctor_get(v_toApplicative_2234_, 0);
v_toSeq_2236_ = lean_ctor_get(v_toApplicative_2234_, 2);
v_toSeqLeft_2237_ = lean_ctor_get(v_toApplicative_2234_, 3);
v_toSeqRight_2238_ = lean_ctor_get(v_toApplicative_2234_, 4);
v___f_2239_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2240_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2235_, 2);
v___f_2241_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2241_, 0, v_toFunctor_2235_);
v___f_2242_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2242_, 0, v_toFunctor_2235_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___f_2241_);
lean_ctor_set(v___x_2243_, 1, v___f_2242_);
lean_inc(v_toSeqRight_2238_);
v___f_2244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2244_, 0, v_toSeqRight_2238_);
lean_inc(v_toSeqLeft_2237_);
v___f_2245_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2245_, 0, v_toSeqLeft_2237_);
lean_inc(v_toSeq_2236_);
v___f_2246_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2246_, 0, v_toSeq_2236_);
v___x_2247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2243_);
lean_ctor_set(v___x_2247_, 1, v___f_2239_);
lean_ctor_set(v___x_2247_, 2, v___f_2246_);
lean_ctor_set(v___x_2247_, 3, v___f_2245_);
lean_ctor_set(v___x_2247_, 4, v___f_2244_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___f_2240_);
v___x_2249_ = l_StateRefT_x27_instMonad___redArg(v___x_2248_);
v_toApplicative_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v___x_2249_, 1);
lean_dec(v_unused_2283_);
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2282_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_toApplicative_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2282_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_toFunctor_2254_; lean_object* v_toSeq_2255_; lean_object* v_toSeqLeft_2256_; lean_object* v_toSeqRight_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2280_; 
v_toFunctor_2254_ = lean_ctor_get(v_toApplicative_2250_, 0);
v_toSeq_2255_ = lean_ctor_get(v_toApplicative_2250_, 2);
v_toSeqLeft_2256_ = lean_ctor_get(v_toApplicative_2250_, 3);
v_toSeqRight_2257_ = lean_ctor_get(v_toApplicative_2250_, 4);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_toApplicative_2250_);
if (v_isSharedCheck_2280_ == 0)
{
lean_object* v_unused_2281_; 
v_unused_2281_ = lean_ctor_get(v_toApplicative_2250_, 1);
lean_dec(v_unused_2281_);
v___x_2259_ = v_toApplicative_2250_;
v_isShared_2260_ = v_isSharedCheck_2280_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_toSeqRight_2257_);
lean_inc(v_toSeqLeft_2256_);
lean_inc(v_toSeq_2255_);
lean_inc(v_toFunctor_2254_);
lean_dec(v_toApplicative_2250_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2280_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___f_2266_; lean_object* v___f_2267_; lean_object* v___f_2268_; lean_object* v___x_2270_; 
v___f_2261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2254_);
v___f_2263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2263_, 0, v_toFunctor_2254_);
v___f_2264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2264_, 0, v_toFunctor_2254_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___f_2263_);
lean_ctor_set(v___x_2265_, 1, v___f_2264_);
v___f_2266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2266_, 0, v_toSeqRight_2257_);
v___f_2267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2267_, 0, v_toSeqLeft_2256_);
v___f_2268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2268_, 0, v_toSeq_2255_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 4, v___f_2266_);
lean_ctor_set(v___x_2259_, 3, v___f_2267_);
lean_ctor_set(v___x_2259_, 2, v___f_2268_);
lean_ctor_set(v___x_2259_, 1, v___f_2261_);
lean_ctor_set(v___x_2259_, 0, v___x_2265_);
v___x_2270_ = v___x_2259_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v___f_2261_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v___f_2268_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v___f_2267_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v___f_2266_);
v___x_2270_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v___f_2262_);
lean_ctor_set(v___x_2252_, 0, v___x_2270_);
v___x_2272_ = v___x_2252_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___f_2262_);
v___x_2272_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_23469__overap_2276_; lean_object* v___x_2277_; 
v___x_2273_ = l_StateRefT_x27_instMonad___redArg(v___x_2272_);
v___x_2274_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2275_ = l_instInhabitedOfMonad___redArg(v___x_2273_, v___x_2274_);
v___x_23469__overap_2276_ = lean_panic_fn_borrowed(v___x_2275_, v_msg_2226_);
lean_dec(v___x_2275_);
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
v___x_2277_ = lean_apply_6(v___x_23469__overap_2276_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, lean_box(0));
return v___x_2277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
return v_res_2291_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2296_ = lean_unsigned_to_nat(0u);
v___x_2297_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
lean_ctor_set(v___x_2297_, 2, v___x_2296_);
lean_ctor_set(v___x_2297_, 3, v___x_2296_);
lean_ctor_set(v___x_2297_, 4, v___x_2295_);
lean_ctor_set(v___x_2297_, 5, v___x_2295_);
lean_ctor_set(v___x_2297_, 6, v___x_2295_);
lean_ctor_set(v___x_2297_, 7, v___x_2295_);
lean_ctor_set(v___x_2297_, 8, v___x_2295_);
lean_ctor_set(v___x_2297_, 9, v___x_2295_);
lean_ctor_set(v___x_2297_, 10, v___x_2295_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_unsigned_to_nat(32u);
v___x_2299_ = lean_mk_empty_array_with_capacity(v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = ((size_t)5ULL);
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_unsigned_to_nat(32u);
v___x_2304_ = lean_mk_empty_array_with_capacity(v___x_2303_);
v___x_2305_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2306_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2304_);
lean_ctor_set(v___x_2306_, 2, v___x_2302_);
lean_ctor_set(v___x_2306_, 3, v___x_2302_);
lean_ctor_set_usize(v___x_2306_, 4, v___x_2301_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2307_ = lean_box(1);
v___x_2308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___x_2308_);
lean_ctor_set(v___x_2310_, 2, v___x_2307_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2325_ = l_Lean_stringToMessageData(v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2328_ = l_Lean_stringToMessageData(v___x_2327_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2332_, lean_object* v_declHint_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v_env_2338_; uint8_t v___x_2339_; 
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_st_ref_get(v___y_2334_);
v_env_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc_ref(v_env_2338_);
lean_dec(v___x_2337_);
v___x_2339_ = l_Lean_Name_isAnonymous(v_declHint_2333_);
if (v___x_2339_ == 0)
{
uint8_t v_isExporting_2340_; 
v_isExporting_2340_ = lean_ctor_get_uint8(v_env_2338_, sizeof(void*)*8);
if (v_isExporting_2340_ == 0)
{
lean_object* v___x_2341_; 
lean_dec_ref(v_env_2338_);
lean_dec(v_declHint_2333_);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_msg_2332_);
return v___x_2341_;
}
else
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
lean_inc_ref(v_env_2338_);
v___x_2342_ = l_Lean_Environment_setExporting(v_env_2338_, v___x_2339_);
lean_inc(v_declHint_2333_);
lean_inc_ref(v___x_2342_);
v___x_2343_ = l_Lean_Environment_contains(v___x_2342_, v_declHint_2333_, v_isExporting_2340_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
lean_dec_ref(v___x_2342_);
lean_dec_ref(v_env_2338_);
lean_dec(v_declHint_2333_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_msg_2332_);
return v___x_2344_;
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v_c_2350_; lean_object* v___x_2351_; 
v___x_2345_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2346_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2347_ = l_Lean_Options_empty;
v___x_2348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2342_);
lean_ctor_set(v___x_2348_, 1, v___x_2345_);
lean_ctor_set(v___x_2348_, 2, v___x_2346_);
lean_ctor_set(v___x_2348_, 3, v___x_2347_);
lean_inc(v_declHint_2333_);
v___x_2349_ = l_Lean_MessageData_ofConstName(v_declHint_2333_, v___x_2339_);
v_c_2350_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2350_, 0, v___x_2348_);
lean_ctor_set(v_c_2350_, 1, v___x_2349_);
v___x_2351_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2338_, v_declHint_2333_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec_ref(v_env_2338_);
lean_dec(v_declHint_2333_);
v___x_2352_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v_c_2350_);
v___x_2354_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = l_Lean_MessageData_note(v___x_2355_);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_msg_2332_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
else
{
lean_object* v_val_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2393_; 
v_val_2359_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2361_ = v___x_2351_;
v_isShared_2362_ = v_isSharedCheck_2393_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_val_2359_);
lean_dec(v___x_2351_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2393_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v_mod_2365_; uint8_t v___x_2366_; 
v___x_2363_ = l_Lean_Environment_header(v_env_2338_);
lean_dec_ref(v_env_2338_);
v___x_2364_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2363_);
v_mod_2365_ = lean_array_get(v___x_2336_, v___x_2364_, v_val_2359_);
lean_dec(v_val_2359_);
lean_dec_ref(v___x_2364_);
v___x_2366_ = l_Lean_isPrivateName(v_declHint_2333_);
lean_dec(v_declHint_2333_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v_c_2350_);
v___x_2369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = l_Lean_MessageData_ofName(v_mod_2365_);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_Lean_MessageData_note(v___x_2374_);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_msg_2332_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set_tag(v___x_2361_, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2376_);
v___x_2378_ = v___x_2361_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v_c_2350_);
v___x_2382_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_MessageData_ofName(v_mod_2365_);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = l_Lean_MessageData_note(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_msg_2332_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set_tag(v___x_2361_, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2389_);
v___x_2391_ = v___x_2361_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2394_; 
lean_dec_ref(v_env_2338_);
lean_dec(v_declHint_2333_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_msg_2332_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2395_, lean_object* v_declHint_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2395_, v_declHint_2396_, v___y_2397_);
lean_dec(v___y_2397_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2400_, lean_object* v_declHint_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2408_; lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2418_; 
v___x_2408_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2400_, v_declHint_2401_, v___y_2406_);
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2418_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2418_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2413_ = l_Lean_unknownIdentifierMessageTag;
v___x_2414_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v_a_2409_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2414_);
v___x_2416_ = v___x_2411_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2419_, lean_object* v_declHint_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2419_, v_declHint_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_ref_2434_; lean_object* v___x_2435_; lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2444_; 
v_ref_2434_ = lean_ctor_get(v___y_2431_, 2);
v___x_2435_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_inc(v_ref_2434_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_ref_2434_);
lean_ctor_set(v___x_2440_, 1, v_a_2436_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 1);
lean_ctor_set(v___x_2438_, 0, v___x_2440_);
v___x_2442_ = v___x_2438_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2452_, lean_object* v_msg_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_toCold_2460_; lean_object* v_currRecDepth_2461_; lean_object* v_ref_2462_; uint8_t v_diag_2463_; uint8_t v_suppressElabErrors_2464_; lean_object* v_ref_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_toCold_2460_ = lean_ctor_get(v___y_2457_, 0);
v_currRecDepth_2461_ = lean_ctor_get(v___y_2457_, 1);
v_ref_2462_ = lean_ctor_get(v___y_2457_, 2);
v_diag_2463_ = lean_ctor_get_uint8(v___y_2457_, sizeof(void*)*3);
v_suppressElabErrors_2464_ = lean_ctor_get_uint8(v___y_2457_, sizeof(void*)*3 + 1);
v_ref_2465_ = l_Lean_replaceRef(v_ref_2452_, v_ref_2462_);
lean_inc(v_currRecDepth_2461_);
lean_inc_ref(v_toCold_2460_);
v___x_2466_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2466_, 0, v_toCold_2460_);
lean_ctor_set(v___x_2466_, 1, v_currRecDepth_2461_);
lean_ctor_set(v___x_2466_, 2, v_ref_2465_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*3, v_diag_2463_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*3 + 1, v_suppressElabErrors_2464_);
v___x_2467_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2453_, v___y_2455_, v___y_2456_, v___x_2466_, v___y_2458_);
lean_dec_ref_known(v___x_2466_, 3);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2468_, lean_object* v_msg_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2468_, v_msg_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec(v_ref_2468_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2477_, lean_object* v_msg_2478_, lean_object* v_declHint_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; lean_object* v_a_2487_; lean_object* v___x_2488_; 
v___x_2486_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2478_, v_declHint_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref(v___x_2486_);
v___x_2488_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2477_, v_a_2487_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2489_, lean_object* v_msg_2490_, lean_object* v_declHint_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2489_, v_msg_2490_, v_declHint_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec(v_ref_2489_);
return v_res_2498_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2501_ = l_Lean_stringToMessageData(v___x_2500_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2504_ = l_Lean_stringToMessageData(v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2505_, lean_object* v_constName_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2513_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2514_ = 0;
lean_inc(v_constName_2506_);
v___x_2515_ = l_Lean_MessageData_ofConstName(v_constName_2506_, v___x_2514_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2513_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2505_, v___x_2518_, v_constName_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2520_, lean_object* v_constName_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2520_, v_constName_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec(v_ref_2520_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_ref_2536_; lean_object* v___x_2537_; 
v_ref_2536_ = lean_ctor_get(v___y_2533_, 2);
v___x_2537_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2536_, v_constName_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; lean_object* v_env_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; 
v___x_2553_ = lean_st_ref_get(v___y_2551_);
v_env_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc_ref(v_env_2554_);
lean_dec(v___x_2553_);
v___x_2555_ = 0;
lean_inc(v_constName_2546_);
v___x_2556_ = l_Lean_Environment_find_x3f(v_env_2554_, v_constName_2546_, v___x_2555_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2557_;
}
else
{
lean_object* v_val_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_constName_2546_);
v_val_2558_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2556_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_val_2558_);
lean_dec(v___x_2556_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set_tag(v___x_2560_, 0);
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_val_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
return v_res_2573_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2578_ = lean_unsigned_to_nat(53u);
v___x_2579_ = lean_unsigned_to_nat(62u);
v___x_2580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2582_ = l_mkPanicMessageWithDecl(v___x_2581_, v___x_2580_, v___x_2579_, v___x_2578_, v___x_2577_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2583_, size_t v_i_2584_, lean_object* v_bs_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
uint8_t v___x_2592_; 
v___x_2592_ = lean_usize_dec_lt(v_i_2584_, v_sz_2583_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_bs_2585_);
return v___x_2593_;
}
else
{
lean_object* v_v_2594_; lean_object* v___x_2595_; lean_object* v_bs_x27_2596_; lean_object* v_a_2598_; lean_object* v___x_2603_; 
v_v_2594_ = lean_array_uget(v_bs_2585_, v_i_2584_);
v___x_2595_ = lean_unsigned_to_nat(0u);
v_bs_x27_2596_ = lean_array_uset(v_bs_2585_, v_i_2584_, v___x_2595_);
v___x_2603_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2594_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
if (lean_obj_tag(v_a_2604_) == 6)
{
lean_object* v_val_2605_; lean_object* v_numFields_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; 
v_val_2605_ = lean_ctor_get(v_a_2604_, 0);
lean_inc_ref(v_val_2605_);
lean_dec_ref_known(v_a_2604_, 1);
v_numFields_2606_ = lean_ctor_get(v_val_2605_, 4);
lean_inc(v_numFields_2606_);
lean_dec_ref(v_val_2605_);
v___x_2607_ = 0;
v___x_2608_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2608_, 0, v_numFields_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2595_);
lean_ctor_set_uint8(v___x_2608_, sizeof(void*)*2, v___x_2607_);
v_a_2598_ = v___x_2608_;
goto v___jp_2597_;
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec(v_a_2604_);
v___x_2609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2610_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2609_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v_a_2598_ = v_a_2611_;
goto v___jp_2597_;
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_bs_x27_2596_);
v_a_2612_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2610_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2610_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v_bs_x27_2596_);
v_a_2620_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2603_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2603_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
v___jp_2597_:
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((size_t)1ULL);
v___x_2600_ = lean_usize_add(v_i_2584_, v___x_2599_);
v___x_2601_ = lean_array_uset(v_bs_x27_2596_, v_i_2584_, v_a_2598_);
v_i_2584_ = v___x_2600_;
v_bs_2585_ = v___x_2601_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2628_, lean_object* v_i_2629_, lean_object* v_bs_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2628_);
lean_dec(v_sz_2628_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2629_);
lean_dec(v_i_2629_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2637_, v_i_boxed_2638_, v_bs_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
return v_res_2639_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_unsigned_to_nat(16u);
v___x_2642_ = lean_mk_array(v___x_2641_, v___x_2640_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
lean_ctor_set(v___x_2645_, 1, v___x_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2648_, uint8_t v_alsoCasesOn_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v___x_2659_; 
v___x_2659_ = l_Lean_Expr_isApp(v_e_2648_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec_ref(v_e_2648_);
v___x_2660_ = lean_box(0);
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
return v___x_2661_;
}
else
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Expr_getAppFn(v_e_2648_);
if (lean_obj_tag(v___x_2662_) == 4)
{
lean_object* v_declName_2663_; lean_object* v_us_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2819_; 
v_declName_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc_n(v_declName_2663_, 2);
v_us_2664_ = lean_ctor_get(v___x_2662_, 1);
lean_inc(v_us_2664_);
lean_dec_ref_known(v___x_2662_, 2);
v___x_2665_ = l_Lean_instInhabitedExpr;
v___x_2666_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2663_, v___y_2654_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2819_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2819_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
if (lean_obj_tag(v_a_2667_) == 1)
{
lean_object* v_val_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2712_; 
v_val_2671_ = lean_ctor_get(v_a_2667_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_a_2667_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2673_ = v_a_2667_;
v_isShared_2674_ = v_isSharedCheck_2712_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_val_2671_);
lean_dec(v_a_2667_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2712_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v_dummy_2675_; lean_object* v_nargs_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v_args_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_dummy_2675_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2676_ = l_Lean_Expr_getAppNumArgs(v_e_2648_);
lean_inc(v_nargs_2676_);
v___x_2677_ = lean_mk_array(v_nargs_2676_, v_dummy_2675_);
v___x_2678_ = lean_unsigned_to_nat(1u);
v___x_2679_ = lean_nat_sub(v_nargs_2676_, v___x_2678_);
lean_dec(v_nargs_2676_);
v_args_2680_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2648_, v___x_2677_, v___x_2679_);
v___x_2681_ = lean_array_get_size(v_args_2680_);
v___x_2682_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2671_);
v___x_2683_ = lean_nat_dec_lt(v___x_2681_, v___x_2682_);
lean_dec(v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v_numParams_2684_; lean_object* v_numDiscrs_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v_numParams_2684_ = lean_ctor_get(v_val_2671_, 0);
v_numDiscrs_2685_ = lean_ctor_get(v_val_2671_, 1);
v___x_2686_ = lean_array_mk(v_us_2664_);
v___x_2687_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2684_);
v___x_2688_ = l_Array_extract___redArg(v_args_2680_, v___x_2687_, v_numParams_2684_);
v___x_2689_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2671_);
v___x_2690_ = lean_array_get(v___x_2665_, v_args_2680_, v___x_2689_);
lean_dec(v___x_2689_);
v___x_2691_ = lean_nat_add(v_numParams_2684_, v___x_2678_);
v___x_2692_ = lean_nat_add(v___x_2691_, v_numDiscrs_2685_);
lean_inc(v___x_2692_);
lean_inc_ref_n(v_args_2680_, 2);
v___x_2693_ = l_Array_toSubarray___redArg(v_args_2680_, v___x_2691_, v___x_2692_);
v___x_2694_ = l_Subarray_copy___redArg(v___x_2693_);
v___x_2695_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2671_);
v___x_2696_ = lean_nat_add(v___x_2692_, v___x_2695_);
lean_dec(v___x_2695_);
lean_inc(v___x_2696_);
v___x_2697_ = l_Array_toSubarray___redArg(v_args_2680_, v___x_2692_, v___x_2696_);
v___x_2698_ = l_Subarray_copy___redArg(v___x_2697_);
v___x_2699_ = l_Array_toSubarray___redArg(v_args_2680_, v___x_2696_, v___x_2681_);
v___x_2700_ = l_Subarray_copy___redArg(v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2701_, 0, v_val_2671_);
lean_ctor_set(v___x_2701_, 1, v_declName_2663_);
lean_ctor_set(v___x_2701_, 2, v___x_2686_);
lean_ctor_set(v___x_2701_, 3, v___x_2688_);
lean_ctor_set(v___x_2701_, 4, v___x_2690_);
lean_ctor_set(v___x_2701_, 5, v___x_2694_);
lean_ctor_set(v___x_2701_, 6, v___x_2698_);
lean_ctor_set(v___x_2701_, 7, v___x_2700_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2701_);
v___x_2703_ = v___x_2673_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2703_);
v___x_2705_ = v___x_2669_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
lean_dec_ref(v_args_2680_);
lean_del_object(v___x_2673_);
lean_dec(v_val_2671_);
lean_dec(v_us_2664_);
lean_dec(v_declName_2663_);
v___x_2708_ = lean_box(0);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2708_);
v___x_2710_ = v___x_2669_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v___x_2713_; 
lean_del_object(v___x_2669_);
lean_dec(v_a_2667_);
v___x_2713_ = lean_st_ref_get(v___y_2654_);
if (v_alsoCasesOn_2649_ == 0)
{
lean_dec(v___x_2713_);
lean_dec(v_us_2664_);
lean_dec(v_declName_2663_);
lean_dec_ref(v_e_2648_);
goto v___jp_2656_;
}
else
{
lean_object* v_env_2714_; uint8_t v___x_2715_; 
v_env_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc_ref(v_env_2714_);
lean_dec(v___x_2713_);
lean_inc(v_declName_2663_);
v___x_2715_ = l_Lean_isCasesOnRecursor(v_env_2714_, v_declName_2663_);
if (v___x_2715_ == 0)
{
lean_dec(v_us_2664_);
lean_dec(v_declName_2663_);
lean_dec_ref(v_e_2648_);
goto v___jp_2656_;
}
else
{
lean_object* v_indName_2716_; lean_object* v___x_2717_; 
v_indName_2716_ = l_Lean_Name_getPrefix(v_declName_2663_);
v___x_2717_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2716_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2810_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2810_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2810_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
if (lean_obj_tag(v_a_2718_) == 5)
{
lean_object* v_val_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2805_; 
v_val_2722_ = lean_ctor_get(v_a_2718_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_a_2718_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2724_ = v_a_2718_;
v_isShared_2725_ = v_isSharedCheck_2805_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_val_2722_);
lean_dec(v_a_2718_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2805_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_toConstantVal_2726_; lean_object* v_numParams_2727_; lean_object* v_numIndices_2728_; lean_object* v_ctors_2729_; lean_object* v_nargs_2730_; lean_object* v_dummy_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v_args_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v_toConstantVal_2726_ = lean_ctor_get(v_val_2722_, 0);
lean_inc_ref(v_toConstantVal_2726_);
v_numParams_2727_ = lean_ctor_get(v_val_2722_, 1);
lean_inc(v_numParams_2727_);
v_numIndices_2728_ = lean_ctor_get(v_val_2722_, 2);
lean_inc(v_numIndices_2728_);
v_ctors_2729_ = lean_ctor_get(v_val_2722_, 4);
lean_inc(v_ctors_2729_);
v_nargs_2730_ = l_Lean_Expr_getAppNumArgs(v_e_2648_);
v_dummy_2731_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2730_);
v___x_2732_ = lean_mk_array(v_nargs_2730_, v_dummy_2731_);
v___x_2733_ = lean_unsigned_to_nat(1u);
v___x_2734_ = lean_nat_sub(v_nargs_2730_, v___x_2733_);
lean_dec(v_nargs_2730_);
v_args_2735_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2648_, v___x_2732_, v___x_2734_);
v___x_2736_ = lean_nat_add(v_numParams_2727_, v___x_2733_);
v___x_2737_ = lean_nat_add(v___x_2736_, v_numIndices_2728_);
v___x_2738_ = lean_nat_add(v___x_2737_, v___x_2733_);
lean_dec(v___x_2737_);
v___x_2739_ = l_Lean_InductiveVal_numCtors(v_val_2722_);
lean_dec_ref(v_val_2722_);
v___x_2740_ = lean_nat_add(v___x_2738_, v___x_2739_);
lean_dec(v___x_2739_);
v___x_2741_ = lean_array_get_size(v_args_2735_);
v___x_2742_ = lean_nat_dec_le(v___x_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2745_; 
lean_dec(v___x_2740_);
lean_dec(v___x_2738_);
lean_dec(v___x_2736_);
lean_dec_ref(v_args_2735_);
lean_dec(v_ctors_2729_);
lean_dec(v_numIndices_2728_);
lean_dec(v_numParams_2727_);
lean_dec_ref(v_toConstantVal_2726_);
lean_del_object(v___x_2724_);
lean_dec(v_us_2664_);
lean_dec(v_declName_2663_);
v___x_2743_ = lean_box(0);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2743_);
v___x_2745_ = v___x_2720_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
else
{
lean_object* v___x_2747_; lean_object* v_params_2748_; lean_object* v_motive_2749_; lean_object* v_discrs_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v_discrInfos_2753_; lean_object* v_alts_2754_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_lower_2796_; lean_object* v_upper_2797_; uint8_t v___x_2804_; 
lean_del_object(v___x_2720_);
v___x_2747_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2727_);
lean_inc_ref_n(v_args_2735_, 3);
v_params_2748_ = l_Array_toSubarray___redArg(v_args_2735_, v___x_2747_, v_numParams_2727_);
v_motive_2749_ = lean_array_get(v___x_2665_, v_args_2735_, v_numParams_2727_);
lean_dec(v_numParams_2727_);
lean_inc(v___x_2738_);
v_discrs_2750_ = l_Array_toSubarray___redArg(v_args_2735_, v___x_2736_, v___x_2738_);
v___x_2751_ = lean_nat_add(v_numIndices_2728_, v___x_2733_);
lean_dec(v_numIndices_2728_);
v___x_2752_ = lean_box(0);
v_discrInfos_2753_ = lean_mk_array(v___x_2751_, v___x_2752_);
lean_inc(v___x_2740_);
v_alts_2754_ = l_Array_toSubarray___redArg(v_args_2735_, v___x_2738_, v___x_2740_);
v___x_2804_ = lean_nat_dec_le(v___x_2740_, v___x_2747_);
if (v___x_2804_ == 0)
{
v_lower_2796_ = v___x_2740_;
v_upper_2797_ = v___x_2741_;
goto v___jp_2795_;
}
else
{
lean_dec(v___x_2740_);
v_lower_2796_ = v___x_2747_;
v_upper_2797_ = v___x_2741_;
goto v___jp_2795_;
}
v___jp_2755_:
{
lean_object* v___x_2758_; size_t v_sz_2759_; size_t v___x_2760_; lean_object* v___x_2761_; 
v___x_2758_ = lean_array_mk(v_ctors_2729_);
v_sz_2759_ = lean_array_size(v___x_2758_);
v___x_2760_ = ((size_t)0ULL);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2759_, v___x_2760_, v___x_2758_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2786_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2786_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2786_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_start_2766_; lean_object* v_stop_2767_; lean_object* v_start_2768_; lean_object* v_stop_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v_start_2766_ = lean_ctor_get(v_params_2748_, 1);
lean_inc(v_start_2766_);
v_stop_2767_ = lean_ctor_get(v_params_2748_, 2);
lean_inc(v_stop_2767_);
v_start_2768_ = lean_ctor_get(v_discrs_2750_, 1);
lean_inc(v_start_2768_);
v_stop_2769_ = lean_ctor_get(v_discrs_2750_, 2);
lean_inc(v_stop_2769_);
v___x_2770_ = lean_nat_sub(v_stop_2767_, v_start_2766_);
lean_dec(v_start_2766_);
lean_dec(v_stop_2767_);
v___x_2771_ = lean_nat_sub(v_stop_2769_, v_start_2768_);
lean_dec(v_start_2768_);
lean_dec(v_stop_2769_);
v___x_2772_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2773_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2770_);
lean_ctor_set(v___x_2773_, 1, v___x_2771_);
lean_ctor_set(v___x_2773_, 2, v_a_2762_);
lean_ctor_set(v___x_2773_, 3, v___y_2757_);
lean_ctor_set(v___x_2773_, 4, v_discrInfos_2753_);
lean_ctor_set(v___x_2773_, 5, v___x_2772_);
v___x_2774_ = lean_array_mk(v_us_2664_);
v___x_2775_ = l_Subarray_copy___redArg(v_params_2748_);
v___x_2776_ = l_Subarray_copy___redArg(v_discrs_2750_);
v___x_2777_ = l_Subarray_copy___redArg(v_alts_2754_);
v___x_2778_ = l_Subarray_copy___redArg(v___y_2756_);
v___x_2779_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2773_);
lean_ctor_set(v___x_2779_, 1, v_declName_2663_);
lean_ctor_set(v___x_2779_, 2, v___x_2774_);
lean_ctor_set(v___x_2779_, 3, v___x_2775_);
lean_ctor_set(v___x_2779_, 4, v_motive_2749_);
lean_ctor_set(v___x_2779_, 5, v___x_2776_);
lean_ctor_set(v___x_2779_, 6, v___x_2777_);
lean_ctor_set(v___x_2779_, 7, v___x_2778_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 1);
lean_ctor_set(v___x_2724_, 0, v___x_2779_);
v___x_2781_ = v___x_2724_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2783_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2781_);
v___x_2783_ = v___x_2764_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec_ref(v_alts_2754_);
lean_dec_ref(v_discrInfos_2753_);
lean_dec_ref(v_discrs_2750_);
lean_dec(v_motive_2749_);
lean_dec_ref(v_params_2748_);
lean_del_object(v___x_2724_);
lean_dec(v_us_2664_);
lean_dec(v_declName_2663_);
v_a_2787_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2761_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2761_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
v___jp_2795_:
{
lean_object* v_levelParams_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v_levelParams_2798_ = lean_ctor_get(v_toConstantVal_2726_, 1);
lean_inc(v_levelParams_2798_);
lean_dec_ref(v_toConstantVal_2726_);
v___x_2799_ = l_Array_toSubarray___redArg(v_args_2735_, v_lower_2796_, v_upper_2797_);
v___x_2800_ = l_List_lengthTR___redArg(v_levelParams_2798_);
lean_dec(v_levelParams_2798_);
v___x_2801_ = l_List_lengthTR___redArg(v_us_2664_);
v___x_2802_ = lean_nat_dec_eq(v___x_2800_, v___x_2801_);
lean_dec(v___x_2801_);
lean_dec(v___x_2800_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2756_ = v___x_2799_;
v___y_2757_ = v___x_2803_;
goto v___jp_2755_;
}
else
{
v___y_2756_ = v___x_2799_;
v___y_2757_ = v___x_2752_;
goto v___jp_2755_;
}
}
}
}
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_dec(v_a_2718_);
lean_dec(v_us_2664_);
lean_dec(v_declName_2663_);
lean_dec_ref(v_e_2648_);
v___x_2806_ = lean_box(0);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2806_);
v___x_2808_ = v___x_2720_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_us_2664_);
lean_dec(v_declName_2663_);
lean_dec_ref(v_e_2648_);
v_a_2811_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2717_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2717_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
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
lean_dec_ref(v___x_2662_);
lean_dec_ref(v_e_2648_);
goto v___jp_2656_;
}
}
v___jp_2656_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_box(0);
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2820_, lean_object* v_alsoCasesOn_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2828_; lean_object* v_res_2829_; 
v_alsoCasesOn_boxed_2828_ = lean_unbox(v_alsoCasesOn_2821_);
v_res_2829_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2820_, v_alsoCasesOn_boxed_2828_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
if (lean_obj_tag(v_a_2830_) == 0)
{
lean_object* v___x_2832_; 
v___x_2832_ = l_List_reverse___redArg(v_a_2831_);
return v___x_2832_;
}
else
{
lean_object* v_head_2833_; lean_object* v_tail_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2843_; 
v_head_2833_ = lean_ctor_get(v_a_2830_, 0);
v_tail_2834_ = lean_ctor_get(v_a_2830_, 1);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_a_2830_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2836_ = v_a_2830_;
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_tail_2834_);
lean_inc(v_head_2833_);
lean_dec(v_a_2830_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2838_ = l_Lean_MessageData_ofExpr(v_head_2833_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 1, v_a_2831_);
lean_ctor_set(v___x_2836_, 0, v___x_2838_);
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_a_2831_);
v___x_2840_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
v_a_2830_ = v_tail_2834_;
v_a_2831_ = v___x_2840_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2844_, lean_object* v_x_2845_){
_start:
{
lean_object* v_fnName_2846_; uint8_t v___x_2847_; 
v_fnName_2846_ = lean_ctor_get(v_x_2845_, 0);
v___x_2847_ = l_Lean_Expr_isConstOf(v_x_2844_, v_fnName_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2848_, lean_object* v_x_2849_){
_start:
{
uint8_t v_res_2850_; lean_object* v_r_2851_; 
v_res_2850_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2848_, v_x_2849_);
lean_dec_ref(v_x_2849_);
lean_dec_ref(v_x_2848_);
v_r_2851_ = lean_box(v_res_2850_);
return v_r_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2852_, lean_object* v_type_2853_, lean_object* v_val_2854_, lean_object* v_k_2855_, uint8_t v_nondep_2856_, uint8_t v_kind_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___f_2864_; lean_object* v___x_2865_; 
lean_inc(v___y_2858_);
v___f_2864_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2864_, 0, v_k_2855_);
lean_closure_set(v___f_2864_, 1, v___y_2858_);
v___x_2865_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2852_, v_type_2853_, v_val_2854_, v___f_2864_, v_nondep_2856_, v_kind_2857_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2865_) == 0)
{
return v___x_2865_;
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2874_, lean_object* v_type_2875_, lean_object* v_val_2876_, lean_object* v_k_2877_, lean_object* v_nondep_2878_, lean_object* v_kind_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v_nondep_boxed_2886_; uint8_t v_kind_boxed_2887_; lean_object* v_res_2888_; 
v_nondep_boxed_2886_ = lean_unbox(v_nondep_2878_);
v_kind_boxed_2887_ = lean_unbox(v_kind_2879_);
v_res_2888_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2874_, v_type_2875_, v_val_2876_, v_k_2877_, v_nondep_boxed_2886_, v_kind_boxed_2887_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2889_, uint8_t v_usedLetOnly_2890_, lean_object* v_x_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; 
lean_inc(v___y_2896_);
lean_inc_ref(v___y_2895_);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
lean_inc_ref(v_x_2891_);
v___x_2898_ = lean_apply_7(v_k_2889_, v_x_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, lean_box(0));
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v___x_2900_ = lean_unsigned_to_nat(1u);
v___x_2901_ = lean_mk_empty_array_with_capacity(v___x_2900_);
v___x_2902_ = lean_array_push(v___x_2901_, v_x_2891_);
v___x_2903_ = 0;
v___x_2904_ = 1;
v___x_2905_ = l_Lean_Meta_mkLetFVars(v___x_2902_, v_a_2899_, v_usedLetOnly_2890_, v___x_2903_, v___x_2904_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec_ref(v___x_2902_);
return v___x_2905_;
}
else
{
lean_dec_ref(v_x_2891_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2906_, lean_object* v_usedLetOnly_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v_usedLetOnly_boxed_2915_; lean_object* v_res_2916_; 
v_usedLetOnly_boxed_2915_ = lean_unbox(v_usedLetOnly_2907_);
v_res_2916_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2906_, v_usedLetOnly_boxed_2915_, v_x_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2917_, lean_object* v_type_2918_, lean_object* v_val_2919_, lean_object* v_k_2920_, uint8_t v_nondep_2921_, uint8_t v_kind_2922_, uint8_t v_usedLetOnly_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; lean_object* v___f_2931_; lean_object* v___x_2932_; 
v___x_2930_ = lean_box(v_usedLetOnly_2923_);
v___f_2931_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2931_, 0, v_k_2920_);
lean_closure_set(v___f_2931_, 1, v___x_2930_);
v___x_2932_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2917_, v_type_2918_, v_val_2919_, v___f_2931_, v_nondep_2921_, v_kind_2922_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2933_, lean_object* v_type_2934_, lean_object* v_val_2935_, lean_object* v_k_2936_, lean_object* v_nondep_2937_, lean_object* v_kind_2938_, lean_object* v_usedLetOnly_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
uint8_t v_nondep_boxed_2946_; uint8_t v_kind_boxed_2947_; uint8_t v_usedLetOnly_boxed_2948_; lean_object* v_res_2949_; 
v_nondep_boxed_2946_ = lean_unbox(v_nondep_2937_);
v_kind_boxed_2947_ = lean_unbox(v_kind_2938_);
v_usedLetOnly_boxed_2948_ = lean_unbox(v_usedLetOnly_2939_);
v_res_2949_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2933_, v_type_2934_, v_val_2935_, v_k_2936_, v_nondep_boxed_2946_, v_kind_boxed_2947_, v_usedLetOnly_boxed_2948_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_2950_, lean_object* v_positions_2951_, lean_object* v_recFnNames_2952_, lean_object* v_containsRecFn_2953_, lean_object* v_below_2954_, size_t v_sz_2955_, size_t v_i_2956_, lean_object* v_bs_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
uint8_t v___x_2964_; 
v___x_2964_ = lean_usize_dec_lt(v_i_2956_, v_sz_2955_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref(v_below_2954_);
lean_dec_ref(v_containsRecFn_2953_);
lean_dec_ref(v_recFnNames_2952_);
lean_dec_ref(v_positions_2951_);
lean_dec_ref(v_recArgInfos_2950_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_bs_2957_);
return v___x_2965_;
}
else
{
lean_object* v_v_2966_; lean_object* v___x_2967_; lean_object* v_bs_x27_2968_; lean_object* v___x_2969_; 
v_v_2966_ = lean_array_uget(v_bs_2957_, v_i_2956_);
v___x_2967_ = lean_unsigned_to_nat(0u);
v_bs_x27_2968_ = lean_array_uset(v_bs_2957_, v_i_2956_, v___x_2967_);
lean_inc_ref(v___y_2961_);
lean_inc_ref(v_below_2954_);
lean_inc_ref(v_containsRecFn_2953_);
lean_inc_ref(v_recFnNames_2952_);
lean_inc_ref(v_positions_2951_);
lean_inc_ref(v_recArgInfos_2950_);
v___x_2969_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_2950_, v_positions_2951_, v_recFnNames_2952_, v_containsRecFn_2953_, v_below_2954_, v_v_2966_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_2973_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = ((size_t)1ULL);
v___x_2972_ = lean_usize_add(v_i_2956_, v___x_2971_);
v___x_2973_ = lean_array_uset(v_bs_x27_2968_, v_i_2956_, v_a_2970_);
v_i_2956_ = v___x_2972_;
v_bs_2957_ = v___x_2973_;
goto _start;
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v_bs_x27_2968_);
lean_dec_ref(v_below_2954_);
lean_dec_ref(v_containsRecFn_2953_);
lean_dec_ref(v_recFnNames_2952_);
lean_dec_ref(v_positions_2951_);
lean_dec_ref(v_recArgInfos_2950_);
v_a_2975_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2969_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2969_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_2985_ = l_Lean_stringToMessageData(v___x_2984_);
return v___x_2985_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_2988_ = l_Lean_stringToMessageData(v___x_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_2989_, lean_object* v_positions_2990_, lean_object* v_recFnNames_2991_, lean_object* v_containsRecFn_2992_, lean_object* v_below_2993_, lean_object* v_e_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
if (lean_obj_tag(v_x_2995_) == 5)
{
lean_object* v_fn_3004_; lean_object* v_arg_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_fn_3004_ = lean_ctor_get(v_x_2995_, 0);
lean_inc_ref(v_fn_3004_);
v_arg_3005_ = lean_ctor_get(v_x_2995_, 1);
lean_inc_ref(v_arg_3005_);
lean_dec_ref_known(v_x_2995_, 2);
v___x_3006_ = lean_array_set(v_x_2996_, v_x_2997_, v_arg_3005_);
v___x_3007_ = lean_unsigned_to_nat(1u);
v___x_3008_ = lean_nat_sub(v_x_2997_, v___x_3007_);
lean_dec(v_x_2997_);
v_x_2995_ = v_fn_3004_;
v_x_2996_ = v___x_3006_;
v_x_2997_ = v___x_3008_;
goto _start;
}
else
{
lean_object* v___f_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec(v_x_2997_);
lean_inc_ref(v_x_2995_);
v___f_3010_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3010_, 0, v_x_2995_);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3010_, v_recArgInfos_2989_, v___x_3011_);
if (lean_obj_tag(v___x_3012_) == 1)
{
lean_object* v_val_3013_; lean_object* v___x_3014_; lean_object* v___y_3016_; lean_object* v_recArgPos_3042_; lean_object* v_indGroupInst_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
lean_dec_ref(v_x_2995_);
v_val_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_val_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = lean_array_fget_borrowed(v_recArgInfos_2989_, v_val_3013_);
v_recArgPos_3042_ = lean_ctor_get(v___x_3014_, 2);
v_indGroupInst_3043_ = lean_ctor_get(v___x_3014_, 4);
v___x_3044_ = lean_array_get_size(v_x_2996_);
v___x_3045_ = lean_nat_dec_lt(v_recArgPos_3042_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_dec(v_val_3013_);
lean_dec_ref(v_x_2996_);
lean_dec_ref(v_below_2993_);
lean_dec_ref(v_containsRecFn_2992_);
lean_dec_ref(v_recFnNames_2991_);
lean_dec_ref(v_positions_2990_);
lean_dec_ref(v_recArgInfos_2989_);
v___x_3046_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3047_ = l_Lean_indentExpr(v_e_2994_);
v___x_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3048_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_array_fget_borrowed(v_x_2996_, v_recArgPos_3042_);
lean_inc_ref(v___y_3001_);
lean_inc(v___x_3050_);
lean_inc_ref(v_below_2993_);
lean_inc_ref(v_containsRecFn_2992_);
lean_inc_ref(v_recFnNames_2991_);
lean_inc_ref(v_positions_2990_);
lean_inc_ref(v_recArgInfos_2989_);
v___x_3051_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_2989_, v_positions_2990_, v_recFnNames_2991_, v_containsRecFn_2992_, v_below_2993_, v___x_3050_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v_params_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___x_3051_, 1);
v_params_3053_ = lean_ctor_get(v_indGroupInst_3043_, 2);
v___x_3054_ = lean_array_get_size(v_params_3053_);
lean_inc_ref(v_positions_2990_);
lean_inc_ref(v_below_2993_);
v___x_3055_ = l_Lean_Elab_Structural_toBelow(v_below_2993_, v___x_3054_, v_positions_2990_, v_val_3013_, v_a_3052_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_dec_ref(v_e_2994_);
v___y_3016_ = v___x_3055_;
goto v___jp_3015_;
}
else
{
lean_object* v_a_3056_; uint8_t v___y_3058_; uint8_t v___x_3063_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
v___x_3063_ = l_Lean_Exception_isInterrupt(v_a_3056_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
v___x_3064_ = l_Lean_Exception_isRuntime(v_a_3056_);
v___y_3058_ = v___x_3064_;
goto v___jp_3057_;
}
else
{
lean_dec(v_a_3056_);
v___y_3058_ = v___x_3063_;
goto v___jp_3057_;
}
v___jp_3057_:
{
if (v___y_3058_ == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec_ref_known(v___x_3055_, 1);
v___x_3059_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3060_ = l_Lean_indentExpr(v_e_2994_);
v___x_3061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3061_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
v___y_3016_ = v___x_3062_;
goto v___jp_3015_;
}
else
{
lean_dec_ref(v_e_2994_);
v___y_3016_ = v___x_3055_;
goto v___jp_3015_;
}
}
}
}
else
{
lean_dec(v_val_3013_);
lean_dec_ref(v_x_2996_);
lean_dec_ref(v_e_2994_);
lean_dec_ref(v_below_2993_);
lean_dec_ref(v_containsRecFn_2992_);
lean_dec_ref(v_recFnNames_2991_);
lean_dec_ref(v_positions_2990_);
lean_dec_ref(v_recArgInfos_2989_);
return v___x_3051_;
}
}
v___jp_3015_:
{
if (lean_obj_tag(v___y_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v_fixedParamPerm_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v_snd_3021_; size_t v_sz_3022_; size_t v___x_3023_; lean_object* v___x_3024_; 
v_a_3017_ = lean_ctor_get(v___y_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___y_3016_, 1);
v_fixedParamPerm_3018_ = lean_ctor_get(v___x_3014_, 1);
v___x_3019_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3018_, v_x_2996_);
lean_dec_ref(v_x_2996_);
lean_inc(v___x_3014_);
v___x_3020_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3014_, v___x_3019_);
v_snd_3021_ = lean_ctor_get(v___x_3020_, 1);
lean_inc(v_snd_3021_);
lean_dec_ref(v___x_3020_);
v_sz_3022_ = lean_array_size(v_snd_3021_);
v___x_3023_ = ((size_t)0ULL);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_2989_, v_positions_2990_, v_recFnNames_2991_, v_containsRecFn_2992_, v_below_2993_, v_sz_3022_, v___x_3023_, v_snd_3021_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3033_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3033_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3033_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3029_ = l_Lean_mkAppN(v_a_3017_, v_a_3025_);
lean_dec(v_a_3025_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3029_);
v___x_3031_ = v___x_3027_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_a_3017_);
v_a_3034_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3024_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3024_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_dec_ref(v_x_2996_);
lean_dec_ref(v_below_2993_);
lean_dec_ref(v_containsRecFn_2992_);
lean_dec_ref(v_recFnNames_2991_);
lean_dec_ref(v_positions_2990_);
lean_dec_ref(v_recArgInfos_2989_);
return v___y_3016_;
}
}
}
else
{
lean_object* v___x_3065_; 
lean_dec(v___x_3012_);
lean_dec_ref(v_e_2994_);
lean_inc_ref(v___y_3001_);
lean_inc_ref(v_below_2993_);
lean_inc_ref(v_containsRecFn_2992_);
lean_inc_ref(v_recFnNames_2991_);
lean_inc_ref(v_positions_2990_);
lean_inc_ref(v_recArgInfos_2989_);
v___x_3065_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_2989_, v_positions_2990_, v_recFnNames_2991_, v_containsRecFn_2992_, v_below_2993_, v_x_2995_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; size_t v_sz_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v_sz_3067_ = lean_array_size(v_x_2996_);
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_2989_, v_positions_2990_, v_recFnNames_2991_, v_containsRecFn_2992_, v_below_2993_, v_sz_3067_, v___x_3068_, v_x_2996_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3078_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3078_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3078_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3074_ = l_Lean_mkAppN(v_a_3066_, v_a_3070_);
lean_dec(v_a_3070_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3074_);
v___x_3076_ = v___x_3072_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_a_3066_);
v_a_3079_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3069_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3069_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_dec_ref(v_x_2996_);
lean_dec_ref(v_below_2993_);
lean_dec_ref(v_containsRecFn_2992_);
lean_dec_ref(v_recFnNames_2991_);
lean_dec_ref(v_positions_2990_);
lean_dec_ref(v_recArgInfos_2989_);
return v___x_3065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3087_, lean_object* v_recArgInfos_3088_, lean_object* v_positions_3089_, lean_object* v_recFnNames_3090_, lean_object* v_containsRecFn_3091_, lean_object* v_below_3092_, uint8_t v___x_3093_, uint8_t v_a_3094_, lean_object* v_x_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_expr_instantiate1(v_body_3087_, v_x_3095_);
lean_inc_ref(v___y_3099_);
v___x_3103_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3088_, v_positions_3089_, v_recFnNames_3090_, v_containsRecFn_3091_, v_below_3092_, v___x_3102_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; lean_object* v___x_3109_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = lean_unsigned_to_nat(1u);
v___x_3106_ = lean_mk_empty_array_with_capacity(v___x_3105_);
v___x_3107_ = lean_array_push(v___x_3106_, v_x_3095_);
v___x_3108_ = 1;
v___x_3109_ = l_Lean_Meta_mkLambdaFVars(v___x_3107_, v_a_3104_, v___x_3093_, v_a_3094_, v___x_3093_, v_a_3094_, v___x_3108_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec_ref(v___x_3107_);
return v___x_3109_;
}
else
{
lean_dec_ref(v_x_3095_);
return v___x_3103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3110_, lean_object* v_recArgInfos_3111_, lean_object* v_positions_3112_, lean_object* v_recFnNames_3113_, lean_object* v_containsRecFn_3114_, lean_object* v_below_3115_, lean_object* v___x_3116_, lean_object* v_a_3117_, lean_object* v_x_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
uint8_t v___x_28473__boxed_3125_; uint8_t v_a_28474__boxed_3126_; lean_object* v_res_3127_; 
v___x_28473__boxed_3125_ = lean_unbox(v___x_3116_);
v_a_28474__boxed_3126_ = lean_unbox(v_a_3117_);
v_res_3127_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3110_, v_recArgInfos_3111_, v_positions_3112_, v_recFnNames_3113_, v_containsRecFn_3114_, v_below_3115_, v___x_28473__boxed_3125_, v_a_28474__boxed_3126_, v_x_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v_body_3110_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3128_, lean_object* v_recArgInfos_3129_, lean_object* v_positions_3130_, lean_object* v_recFnNames_3131_, lean_object* v_containsRecFn_3132_, lean_object* v_below_3133_, uint8_t v___x_3134_, uint8_t v_a_3135_, lean_object* v_x_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_expr_instantiate1(v_body_3128_, v_x_3136_);
lean_inc_ref(v___y_3140_);
v___x_3144_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3129_, v_positions_3130_, v_recFnNames_3131_, v_containsRecFn_3132_, v_below_3133_, v___x_3143_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = lean_unsigned_to_nat(1u);
v___x_3147_ = lean_mk_empty_array_with_capacity(v___x_3146_);
v___x_3148_ = lean_array_push(v___x_3147_, v_x_3136_);
v___x_3149_ = 1;
v___x_3150_ = l_Lean_Meta_mkForallFVars(v___x_3148_, v_a_3145_, v___x_3134_, v_a_3135_, v_a_3135_, v___x_3149_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec_ref(v___x_3148_);
return v___x_3150_;
}
else
{
lean_dec_ref(v_x_3136_);
return v___x_3144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3151_, lean_object* v_recArgInfos_3152_, lean_object* v_positions_3153_, lean_object* v_recFnNames_3154_, lean_object* v_containsRecFn_3155_, lean_object* v_below_3156_, lean_object* v___x_3157_, lean_object* v_a_3158_, lean_object* v_x_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
uint8_t v___x_28491__boxed_3166_; uint8_t v_a_28492__boxed_3167_; lean_object* v_res_3168_; 
v___x_28491__boxed_3166_ = lean_unbox(v___x_3157_);
v_a_28492__boxed_3167_ = lean_unbox(v_a_3158_);
v_res_3168_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3151_, v_recArgInfos_3152_, v_positions_3153_, v_recFnNames_3154_, v_containsRecFn_3155_, v_below_3156_, v___x_28491__boxed_3166_, v_a_28492__boxed_3167_, v_x_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v_body_3151_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3169_, lean_object* v_recArgInfos_3170_, lean_object* v_positions_3171_, lean_object* v_recFnNames_3172_, lean_object* v_containsRecFn_3173_, lean_object* v_below_3174_, lean_object* v_x_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3169_, v_recArgInfos_3170_, v_positions_3171_, v_recFnNames_3172_, v_containsRecFn_3173_, v_below_3174_, v_x_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v_x_3175_);
lean_dec_ref(v_body_3169_);
return v_res_3182_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
return v___x_3187_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3190_ = l_Lean_stringToMessageData(v___x_3189_);
return v___x_3190_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3193_ = l_Lean_stringToMessageData(v___x_3192_);
return v___x_3193_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3196_ = l_Lean_stringToMessageData(v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v___x_3197_, lean_object* v_b_3198_, lean_object* v_recArgInfos_3199_, lean_object* v_positions_3200_, lean_object* v_recFnNames_3201_, lean_object* v_containsRecFn_3202_, uint8_t v___x_3203_, uint8_t v_a_3204_, lean_object* v___x_3205_, lean_object* v_a_3206_, lean_object* v_e_3207_, lean_object* v___x_3208_, lean_object* v_xs_3209_, lean_object* v_altBody_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v_toCold_3252_; lean_object* v_options_3253_; uint8_t v_hasTrace_3254_; 
v_toCold_3252_ = lean_ctor_get(v___y_3214_, 0);
v_options_3253_ = lean_ctor_get(v_toCold_3252_, 2);
v_hasTrace_3254_ = lean_ctor_get_uint8(v_options_3253_, sizeof(void*)*1);
if (v_hasTrace_3254_ == 0)
{
lean_dec(v___x_3208_);
v___y_3229_ = v___y_3211_;
v___y_3230_ = v___y_3212_;
v___y_3231_ = v___y_3213_;
v___y_3232_ = v___y_3214_;
v___y_3233_ = v___y_3215_;
goto v___jp_3228_;
}
else
{
lean_object* v_inheritedTraceOptions_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_inheritedTraceOptions_3255_ = lean_ctor_get(v_toCold_3252_, 11);
v___x_3256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3208_);
v___x_3257_ = l_Lean_Name_append(v___x_3256_, v___x_3208_);
v___x_3258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3255_, v_options_3253_, v___x_3257_);
lean_dec(v___x_3257_);
if (v___x_3258_ == 0)
{
lean_dec(v___x_3208_);
v___y_3229_ = v___y_3211_;
v___y_3230_ = v___y_3212_;
v___y_3231_ = v___y_3213_;
v___y_3232_ = v___y_3214_;
v___y_3233_ = v___y_3215_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3259_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3198_);
v___x_3260_ = l_Nat_reprFast(v_b_3198_);
v___x_3261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
v___x_3262_ = l_Lean_MessageData_ofFormat(v___x_3261_);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3259_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
lean_inc_ref(v_xs_3209_);
v___x_3266_ = lean_array_to_list(v_xs_3209_);
v___x_3267_ = lean_box(0);
v___x_3268_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3266_, v___x_3267_);
v___x_3269_ = l_Lean_MessageData_ofList(v___x_3268_);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3265_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3208_, v___x_3270_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_dec_ref_known(v___x_3271_, 1);
v___y_3229_ = v___y_3211_;
v___y_3230_ = v___y_3212_;
v___y_3231_ = v___y_3213_;
v___y_3232_ = v___y_3214_;
v___y_3233_ = v___y_3215_;
goto v___jp_3228_;
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec_ref(v_altBody_3210_);
lean_dec_ref(v_xs_3209_);
lean_dec_ref(v_e_3207_);
lean_dec_ref(v_a_3206_);
lean_dec_ref(v_containsRecFn_3202_);
lean_dec_ref(v_recFnNames_3201_);
lean_dec_ref(v_positions_3200_);
lean_dec_ref(v_recArgInfos_3199_);
lean_dec(v_b_3198_);
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
v___jp_3217_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_array_get_borrowed(v___x_3197_, v_xs_3209_, v_b_3198_);
lean_dec(v_b_3198_);
lean_inc_ref(v___y_3221_);
lean_inc(v___x_3223_);
v___x_3224_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3199_, v_positions_3200_, v_recFnNames_3201_, v_containsRecFn_3202_, v___x_3223_, v_altBody_3210_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v___x_3226_ = 1;
v___x_3227_ = l_Lean_Meta_mkLambdaFVars(v_xs_3209_, v_a_3225_, v___x_3203_, v_a_3204_, v___x_3203_, v_a_3204_, v___x_3226_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec_ref(v_xs_3209_);
return v___x_3227_;
}
else
{
lean_dec_ref(v_xs_3209_);
return v___x_3224_;
}
}
v___jp_3228_:
{
lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3234_ = lean_array_get_size(v_xs_3209_);
v___x_3235_ = lean_nat_dec_eq(v___x_3234_, v___x_3205_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec_ref(v_altBody_3210_);
lean_dec_ref(v_xs_3209_);
lean_dec_ref(v_containsRecFn_3202_);
lean_dec_ref(v_recFnNames_3201_);
lean_dec_ref(v_positions_3200_);
lean_dec_ref(v_recArgInfos_3199_);
lean_dec(v_b_3198_);
v___x_3236_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3237_ = l_Lean_indentExpr(v_a_3206_);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3238_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = l_Lean_indentExpr(v_e_3207_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3242_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
else
{
lean_dec_ref(v_e_3207_);
lean_dec_ref(v_a_3206_);
v___y_3218_ = v___y_3229_;
v___y_3219_ = v___y_3230_;
v___y_3220_ = v___y_3231_;
v___y_3221_ = v___y_3232_;
v___y_3222_ = v___y_3233_;
goto v___jp_3217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v___x_3280_ = _args[0];
lean_object* v_b_3281_ = _args[1];
lean_object* v_recArgInfos_3282_ = _args[2];
lean_object* v_positions_3283_ = _args[3];
lean_object* v_recFnNames_3284_ = _args[4];
lean_object* v_containsRecFn_3285_ = _args[5];
lean_object* v___x_3286_ = _args[6];
lean_object* v_a_3287_ = _args[7];
lean_object* v___x_3288_ = _args[8];
lean_object* v_a_3289_ = _args[9];
lean_object* v_e_3290_ = _args[10];
lean_object* v___x_3291_ = _args[11];
lean_object* v_xs_3292_ = _args[12];
lean_object* v_altBody_3293_ = _args[13];
lean_object* v___y_3294_ = _args[14];
lean_object* v___y_3295_ = _args[15];
lean_object* v___y_3296_ = _args[16];
lean_object* v___y_3297_ = _args[17];
lean_object* v___y_3298_ = _args[18];
lean_object* v___y_3299_ = _args[19];
_start:
{
uint8_t v___x_28567__boxed_3300_; uint8_t v_a_28568__boxed_3301_; lean_object* v_res_3302_; 
v___x_28567__boxed_3300_ = lean_unbox(v___x_3286_);
v_a_28568__boxed_3301_ = lean_unbox(v_a_3287_);
v_res_3302_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3280_, v_b_3281_, v_recArgInfos_3282_, v_positions_3283_, v_recFnNames_3284_, v_containsRecFn_3285_, v___x_28567__boxed_3300_, v_a_28568__boxed_3301_, v___x_3288_, v_a_3289_, v_e_3290_, v___x_3291_, v_xs_3292_, v_altBody_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___x_3288_);
lean_dec_ref(v___x_3280_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3303_, lean_object* v_positions_3304_, lean_object* v_recFnNames_3305_, lean_object* v_containsRecFn_3306_, uint8_t v_a_3307_, lean_object* v_e_3308_, lean_object* v_as_3309_, lean_object* v_bs_3310_, lean_object* v_i_3311_, lean_object* v_cs_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = lean_array_get_size(v_as_3309_);
v___x_3320_ = lean_nat_dec_lt(v_i_3311_, v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
lean_dec(v_i_3311_);
lean_dec_ref(v_e_3308_);
lean_dec_ref(v_containsRecFn_3306_);
lean_dec_ref(v_recFnNames_3305_);
lean_dec_ref(v_positions_3304_);
lean_dec_ref(v_recArgInfos_3303_);
v___x_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_cs_3312_);
return v___x_3321_;
}
else
{
lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3322_ = lean_array_get_size(v_bs_3310_);
v___x_3323_ = lean_nat_dec_lt(v_i_3311_, v___x_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; 
lean_dec(v_i_3311_);
lean_dec_ref(v_e_3308_);
lean_dec_ref(v_containsRecFn_3306_);
lean_dec_ref(v_recFnNames_3305_);
lean_dec_ref(v_positions_3304_);
lean_dec_ref(v_recArgInfos_3303_);
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v_cs_3312_);
return v___x_3324_;
}
else
{
lean_object* v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; lean_object* v_a_3328_; lean_object* v_b_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___f_3334_; lean_object* v___x_3335_; 
v___x_3325_ = l_Lean_instInhabitedExpr;
v___x_3326_ = 0;
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3328_ = lean_array_fget_borrowed(v_as_3309_, v_i_3311_);
v_b_3329_ = lean_array_fget_borrowed(v_bs_3310_, v_i_3311_);
v___x_3330_ = lean_unsigned_to_nat(1u);
v___x_3331_ = lean_nat_add(v_b_3329_, v___x_3330_);
v___x_3332_ = lean_box(v___x_3326_);
v___x_3333_ = lean_box(v_a_3307_);
lean_inc_ref(v_e_3308_);
lean_inc_n(v_a_3328_, 2);
lean_inc(v___x_3331_);
lean_inc_ref(v_containsRecFn_3306_);
lean_inc_ref(v_recFnNames_3305_);
lean_inc_ref(v_positions_3304_);
lean_inc_ref(v_recArgInfos_3303_);
lean_inc(v_b_3329_);
v___f_3334_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 20, 12);
lean_closure_set(v___f_3334_, 0, v___x_3325_);
lean_closure_set(v___f_3334_, 1, v_b_3329_);
lean_closure_set(v___f_3334_, 2, v_recArgInfos_3303_);
lean_closure_set(v___f_3334_, 3, v_positions_3304_);
lean_closure_set(v___f_3334_, 4, v_recFnNames_3305_);
lean_closure_set(v___f_3334_, 5, v_containsRecFn_3306_);
lean_closure_set(v___f_3334_, 6, v___x_3332_);
lean_closure_set(v___f_3334_, 7, v___x_3333_);
lean_closure_set(v___f_3334_, 8, v___x_3331_);
lean_closure_set(v___f_3334_, 9, v_a_3328_);
lean_closure_set(v___f_3334_, 10, v_e_3308_);
lean_closure_set(v___f_3334_, 11, v___x_3327_);
v___x_3335_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3328_, v___x_3331_, v___f_3334_, v___x_3326_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = lean_nat_add(v_i_3311_, v___x_3330_);
lean_dec(v_i_3311_);
v___x_3338_ = lean_array_push(v_cs_3312_, v_a_3336_);
v_i_3311_ = v___x_3337_;
v_cs_3312_ = v___x_3338_;
goto _start;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec_ref(v_cs_3312_);
lean_dec(v_i_3311_);
lean_dec_ref(v_e_3308_);
lean_dec_ref(v_containsRecFn_3306_);
lean_dec_ref(v_recFnNames_3305_);
lean_dec_ref(v_positions_3304_);
lean_dec_ref(v_recArgInfos_3303_);
v_a_3340_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3335_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3335_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
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
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
return v___x_3350_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3353_ = l_Lean_stringToMessageData(v___x_3352_);
return v___x_3353_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3356_ = l_Lean_stringToMessageData(v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3357_, lean_object* v_positions_3358_, lean_object* v_recFnNames_3359_, lean_object* v_containsRecFn_3360_, lean_object* v_below_3361_, lean_object* v_e_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v_e_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___x_3382_; 
lean_inc_ref(v_containsRecFn_3360_);
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
lean_inc(v_a_3365_);
lean_inc_ref(v_a_3364_);
lean_inc(v_a_3363_);
lean_inc_ref(v_e_3362_);
v___x_3382_ = lean_apply_7(v_containsRecFn_3360_, v_e_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, lean_box(0));
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3596_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3596_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3596_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_unbox(v_a_3383_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3389_; 
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v_e_3362_);
v___x_3389_ = v___x_3385_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_e_3362_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
else
{
uint8_t v___x_3391_; 
lean_del_object(v___x_3385_);
v___x_3391_ = 0;
switch(lean_obj_tag(v_e_3362_))
{
case 6:
{
lean_object* v_binderName_3392_; lean_object* v_binderType_3393_; lean_object* v_body_3394_; uint8_t v_binderInfo_3395_; lean_object* v___x_3396_; lean_object* v___f_3397_; lean_object* v___x_3398_; 
v_binderName_3392_ = lean_ctor_get(v_e_3362_, 0);
lean_inc(v_binderName_3392_);
v_binderType_3393_ = lean_ctor_get(v_e_3362_, 1);
lean_inc_ref(v_binderType_3393_);
v_body_3394_ = lean_ctor_get(v_e_3362_, 2);
lean_inc_ref(v_body_3394_);
v_binderInfo_3395_ = lean_ctor_get_uint8(v_e_3362_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3362_, 3);
v___x_3396_ = lean_box(v___x_3391_);
lean_inc_ref(v_below_3361_);
lean_inc_ref(v_containsRecFn_3360_);
lean_inc_ref(v_recFnNames_3359_);
lean_inc_ref(v_positions_3358_);
lean_inc_ref(v_recArgInfos_3357_);
v___f_3397_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3397_, 0, v_body_3394_);
lean_closure_set(v___f_3397_, 1, v_recArgInfos_3357_);
lean_closure_set(v___f_3397_, 2, v_positions_3358_);
lean_closure_set(v___f_3397_, 3, v_recFnNames_3359_);
lean_closure_set(v___f_3397_, 4, v_containsRecFn_3360_);
lean_closure_set(v___f_3397_, 5, v_below_3361_);
lean_closure_set(v___f_3397_, 6, v___x_3396_);
lean_closure_set(v___f_3397_, 7, v_a_3383_);
lean_inc_ref(v_a_3366_);
v___x_3398_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3357_, v_positions_3358_, v_recFnNames_3359_, v_containsRecFn_3360_, v_below_3361_, v_binderType_3393_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; uint8_t v___x_3400_; lean_object* v___x_3401_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v___x_3400_ = 0;
v___x_3401_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3392_, v_binderInfo_3395_, v_a_3399_, v___f_3397_, v___x_3400_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec_ref(v_a_3366_);
return v___x_3401_;
}
else
{
lean_dec_ref(v___f_3397_);
lean_dec(v_binderName_3392_);
lean_dec_ref(v_a_3366_);
return v___x_3398_;
}
}
case 7:
{
lean_object* v_binderName_3402_; lean_object* v_binderType_3403_; lean_object* v_body_3404_; uint8_t v_binderInfo_3405_; lean_object* v___x_3406_; lean_object* v___f_3407_; lean_object* v___x_3408_; 
v_binderName_3402_ = lean_ctor_get(v_e_3362_, 0);
lean_inc(v_binderName_3402_);
v_binderType_3403_ = lean_ctor_get(v_e_3362_, 1);
lean_inc_ref(v_binderType_3403_);
v_body_3404_ = lean_ctor_get(v_e_3362_, 2);
lean_inc_ref(v_body_3404_);
v_binderInfo_3405_ = lean_ctor_get_uint8(v_e_3362_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3362_, 3);
v___x_3406_ = lean_box(v___x_3391_);
lean_inc_ref(v_below_3361_);
lean_inc_ref(v_containsRecFn_3360_);
lean_inc_ref(v_recFnNames_3359_);
lean_inc_ref(v_positions_3358_);
lean_inc_ref(v_recArgInfos_3357_);
v___f_3407_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3407_, 0, v_body_3404_);
lean_closure_set(v___f_3407_, 1, v_recArgInfos_3357_);
lean_closure_set(v___f_3407_, 2, v_positions_3358_);
lean_closure_set(v___f_3407_, 3, v_recFnNames_3359_);
lean_closure_set(v___f_3407_, 4, v_containsRecFn_3360_);
lean_closure_set(v___f_3407_, 5, v_below_3361_);
lean_closure_set(v___f_3407_, 6, v___x_3406_);
lean_closure_set(v___f_3407_, 7, v_a_3383_);
lean_inc_ref(v_a_3366_);
v___x_3408_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3357_, v_positions_3358_, v_recFnNames_3359_, v_containsRecFn_3360_, v_below_3361_, v_binderType_3403_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; uint8_t v___x_3410_; lean_object* v___x_3411_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v___x_3410_ = 0;
v___x_3411_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3402_, v_binderInfo_3405_, v_a_3409_, v___f_3407_, v___x_3410_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec_ref(v_a_3366_);
return v___x_3411_;
}
else
{
lean_dec_ref(v___f_3407_);
lean_dec(v_binderName_3402_);
lean_dec_ref(v_a_3366_);
return v___x_3408_;
}
}
case 8:
{
lean_object* v_declName_3412_; lean_object* v_type_3413_; lean_object* v_value_3414_; lean_object* v_body_3415_; uint8_t v_nondep_3416_; lean_object* v___f_3417_; lean_object* v___x_3418_; 
lean_dec(v_a_3383_);
v_declName_3412_ = lean_ctor_get(v_e_3362_, 0);
lean_inc(v_declName_3412_);
v_type_3413_ = lean_ctor_get(v_e_3362_, 1);
lean_inc_ref(v_type_3413_);
v_value_3414_ = lean_ctor_get(v_e_3362_, 2);
lean_inc_ref(v_value_3414_);
v_body_3415_ = lean_ctor_get(v_e_3362_, 3);
lean_inc_ref(v_body_3415_);
v_nondep_3416_ = lean_ctor_get_uint8(v_e_3362_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3362_, 4);
lean_inc_ref_n(v_below_3361_, 2);
lean_inc_ref_n(v_containsRecFn_3360_, 2);
lean_inc_ref_n(v_recFnNames_3359_, 2);
lean_inc_ref_n(v_positions_3358_, 2);
lean_inc_ref_n(v_recArgInfos_3357_, 2);
v___f_3417_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3417_, 0, v_body_3415_);
lean_closure_set(v___f_3417_, 1, v_recArgInfos_3357_);
lean_closure_set(v___f_3417_, 2, v_positions_3358_);
lean_closure_set(v___f_3417_, 3, v_recFnNames_3359_);
lean_closure_set(v___f_3417_, 4, v_containsRecFn_3360_);
lean_closure_set(v___f_3417_, 5, v_below_3361_);
lean_inc_ref(v_a_3366_);
v___x_3418_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3357_, v_positions_3358_, v_recFnNames_3359_, v_containsRecFn_3360_, v_below_3361_, v_type_3413_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
lean_inc_ref(v_a_3366_);
v___x_3420_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3357_, v_positions_3358_, v_recFnNames_3359_, v_containsRecFn_3360_, v_below_3361_, v_value_3414_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; uint8_t v___x_3422_; lean_object* v___x_3423_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
v___x_3422_ = 0;
v___x_3423_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3412_, v_a_3419_, v_a_3421_, v___f_3417_, v_nondep_3416_, v___x_3422_, v___x_3391_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec_ref(v_a_3366_);
return v___x_3423_;
}
else
{
lean_dec(v_a_3419_);
lean_dec_ref(v___f_3417_);
lean_dec(v_declName_3412_);
lean_dec_ref(v_a_3366_);
return v___x_3420_;
}
}
else
{
lean_dec_ref(v___f_3417_);
lean_dec_ref(v_value_3414_);
lean_dec(v_declName_3412_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
return v___x_3418_;
}
}
case 10:
{
lean_object* v_data_3424_; lean_object* v_expr_3425_; lean_object* v___x_3426_; 
lean_dec(v_a_3383_);
v_data_3424_ = lean_ctor_get(v_e_3362_, 0);
lean_inc(v_data_3424_);
v_expr_3425_ = lean_ctor_get(v_e_3362_, 1);
lean_inc_ref(v_expr_3425_);
v___x_3426_ = l_Lean_getRecAppSyntax_x3f(v_e_3362_);
lean_dec_ref_known(v_e_3362_, 2);
if (lean_obj_tag(v___x_3426_) == 1)
{
lean_object* v_val_3427_; lean_object* v_toCold_3428_; lean_object* v_currRecDepth_3429_; lean_object* v_ref_3430_; uint8_t v_diag_3431_; uint8_t v_suppressElabErrors_3432_; lean_object* v_ref_3433_; lean_object* v___x_3434_; 
lean_dec(v_data_3424_);
v_val_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_val_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v_toCold_3428_ = lean_ctor_get(v_a_3366_, 0);
lean_inc_ref(v_toCold_3428_);
v_currRecDepth_3429_ = lean_ctor_get(v_a_3366_, 1);
lean_inc(v_currRecDepth_3429_);
v_ref_3430_ = lean_ctor_get(v_a_3366_, 2);
lean_inc(v_ref_3430_);
v_diag_3431_ = lean_ctor_get_uint8(v_a_3366_, sizeof(void*)*3);
v_suppressElabErrors_3432_ = lean_ctor_get_uint8(v_a_3366_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_3366_);
v_ref_3433_ = l_Lean_replaceRef(v_val_3427_, v_ref_3430_);
lean_dec(v_ref_3430_);
lean_dec(v_val_3427_);
v___x_3434_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3434_, 0, v_toCold_3428_);
lean_ctor_set(v___x_3434_, 1, v_currRecDepth_3429_);
lean_ctor_set(v___x_3434_, 2, v_ref_3433_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*3, v_diag_3431_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*3 + 1, v_suppressElabErrors_3432_);
v_e_3362_ = v_expr_3425_;
v_a_3366_ = v___x_3434_;
goto _start;
}
else
{
lean_object* v___x_3436_; 
lean_dec(v___x_3426_);
v___x_3436_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3357_, v_positions_3358_, v_recFnNames_3359_, v_containsRecFn_3360_, v_below_3361_, v_expr_3425_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3445_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3439_ = v___x_3436_;
v_isShared_3440_ = v_isSharedCheck_3445_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3436_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3445_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3441_ = l_Lean_mkMData(v_data_3424_, v_a_3437_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3441_);
v___x_3443_ = v___x_3439_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_dec(v_data_3424_);
return v___x_3436_;
}
}
}
case 11:
{
lean_object* v_typeName_3446_; lean_object* v_idx_3447_; lean_object* v_struct_3448_; lean_object* v___x_3449_; 
lean_dec(v_a_3383_);
v_typeName_3446_ = lean_ctor_get(v_e_3362_, 0);
lean_inc(v_typeName_3446_);
v_idx_3447_ = lean_ctor_get(v_e_3362_, 1);
lean_inc(v_idx_3447_);
v_struct_3448_ = lean_ctor_get(v_e_3362_, 2);
lean_inc_ref(v_struct_3448_);
lean_dec_ref_known(v_e_3362_, 3);
v___x_3449_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3357_, v_positions_3358_, v_recFnNames_3359_, v_containsRecFn_3360_, v_below_3361_, v_struct_3448_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3458_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3458_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3458_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3454_ = l_Lean_mkProj(v_typeName_3446_, v_idx_3447_, v_a_3450_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3454_);
v___x_3456_ = v___x_3452_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
else
{
lean_dec(v_idx_3447_);
lean_dec(v_typeName_3446_);
return v___x_3449_;
}
}
case 5:
{
uint8_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_unbox(v_a_3383_);
lean_inc_ref(v_e_3362_);
v___x_3460_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3362_, v___x_3459_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
if (lean_obj_tag(v_a_3461_) == 0)
{
lean_dec(v_a_3383_);
v_e_3370_ = v_e_3362_;
v___y_3371_ = v_a_3363_;
v___y_3372_ = v_a_3364_;
v___y_3373_ = v_a_3365_;
v___y_3374_ = v_a_3366_;
v___y_3375_ = v_a_3367_;
goto v___jp_3369_;
}
else
{
lean_object* v_val_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; 
v_val_3462_ = lean_ctor_get(v_a_3461_, 0);
lean_inc(v_val_3462_);
lean_dec_ref_known(v_a_3461_, 1);
v___x_3463_ = lean_unsigned_to_nat(0u);
v___x_3464_ = lean_array_get_size(v_recArgInfos_3357_);
v___x_3465_ = lean_nat_dec_lt(v___x_3463_, v___x_3464_);
if (v___x_3465_ == 0)
{
lean_dec(v_val_3462_);
lean_dec(v_a_3383_);
v_e_3370_ = v_e_3362_;
v___y_3371_ = v_a_3363_;
v___y_3372_ = v_a_3364_;
v___y_3373_ = v_a_3365_;
v___y_3374_ = v_a_3366_;
v___y_3375_ = v_a_3367_;
goto v___jp_3369_;
}
else
{
if (v___x_3465_ == 0)
{
lean_dec(v_val_3462_);
lean_dec(v_a_3383_);
v_e_3370_ = v_e_3362_;
v___y_3371_ = v_a_3363_;
v___y_3372_ = v_a_3364_;
v___y_3373_ = v_a_3365_;
v___y_3374_ = v_a_3366_;
v___y_3375_ = v_a_3367_;
goto v___jp_3369_;
}
else
{
size_t v___x_3466_; size_t v___x_3467_; uint8_t v___x_3468_; 
v___x_3466_ = ((size_t)0ULL);
v___x_3467_ = lean_usize_of_nat(v___x_3464_);
v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3362_, v_recArgInfos_3357_, v___x_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_dec(v_val_3462_);
lean_dec(v_a_3383_);
v_e_3370_ = v_e_3362_;
v___y_3371_ = v_a_3363_;
v___y_3372_ = v_a_3364_;
v___y_3373_ = v_a_3365_;
v___y_3374_ = v_a_3366_;
v___y_3375_ = v_a_3367_;
goto v___jp_3369_;
}
else
{
lean_object* v_toCold_3469_; lean_object* v_inheritedTraceOptions_3470_; lean_object* v___x_3471_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___x_3542_; 
v_toCold_3469_ = lean_ctor_get(v_a_3366_, 0);
v_inheritedTraceOptions_3470_ = lean_ctor_get(v_toCold_3469_, 11);
v___x_3471_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3542_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3471_, v_inheritedTraceOptions_3470_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; uint8_t v___x_3544_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v___x_3544_ = lean_unbox(v_a_3543_);
lean_dec(v_a_3543_);
if (v___x_3544_ == 0)
{
v___y_3473_ = v_a_3363_;
v___y_3474_ = v_a_3364_;
v___y_3475_ = v_a_3365_;
v___y_3476_ = v_a_3366_;
v___y_3477_ = v_a_3367_;
goto v___jp_3472_;
}
else
{
lean_object* v___x_3545_; 
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
lean_inc(v_a_3365_);
lean_inc_ref(v_a_3364_);
lean_inc_ref(v_below_3361_);
v___x_3545_ = lean_infer_type(v_below_3361_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3361_);
v___x_3548_ = l_Lean_MessageData_ofExpr(v_below_3361_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = l_Lean_MessageData_ofExpr(v_a_3546_);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3471_, v___x_3553_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_dec_ref_known(v___x_3554_, 1);
v___y_3473_ = v_a_3363_;
v___y_3474_ = v_a_3364_;
v___y_3475_ = v_a_3365_;
v___y_3476_ = v_a_3366_;
v___y_3477_ = v_a_3367_;
goto v___jp_3472_;
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec(v_val_3462_);
lean_dec_ref_known(v_e_3362_, 2);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_dec(v_val_3462_);
lean_dec_ref_known(v_e_3362_, 2);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
return v___x_3545_;
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec(v_val_3462_);
lean_dec_ref_known(v_e_3362_, 2);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
v_a_3563_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3542_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3542_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
v___jp_3472_:
{
lean_object* v___x_3478_; 
lean_inc_ref(v_below_3361_);
v___x_3478_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3462_, v_below_3361_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
if (lean_obj_tag(v_a_3479_) == 1)
{
lean_object* v_val_3480_; lean_object* v_toMatcherInfo_3481_; lean_object* v_matcherName_3482_; lean_object* v_matcherLevels_3483_; lean_object* v_params_3484_; lean_object* v_motive_3485_; lean_object* v_discrs_3486_; lean_object* v_alts_3487_; lean_object* v_remaining_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; lean_object* v___x_3492_; 
lean_dec_ref(v_below_3361_);
v_val_3480_ = lean_ctor_get(v_a_3479_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v_a_3479_, 1);
v_toMatcherInfo_3481_ = lean_ctor_get(v_val_3480_, 0);
lean_inc_ref(v_toMatcherInfo_3481_);
v_matcherName_3482_ = lean_ctor_get(v_val_3480_, 1);
lean_inc(v_matcherName_3482_);
v_matcherLevels_3483_ = lean_ctor_get(v_val_3480_, 2);
lean_inc_ref(v_matcherLevels_3483_);
v_params_3484_ = lean_ctor_get(v_val_3480_, 3);
lean_inc_ref(v_params_3484_);
v_motive_3485_ = lean_ctor_get(v_val_3480_, 4);
lean_inc_ref(v_motive_3485_);
v_discrs_3486_ = lean_ctor_get(v_val_3480_, 5);
lean_inc_ref(v_discrs_3486_);
v_alts_3487_ = lean_ctor_get(v_val_3480_, 6);
lean_inc_ref(v_alts_3487_);
v_remaining_3488_ = lean_ctor_get(v_val_3480_, 7);
lean_inc_ref(v_remaining_3488_);
v___x_3489_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3480_);
v___x_3490_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3491_ = lean_unbox(v_a_3383_);
lean_dec(v_a_3383_);
v___x_3492_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3357_, v_positions_3358_, v_recFnNames_3359_, v_containsRecFn_3360_, v___x_3491_, v_e_3362_, v_alts_3487_, v___x_3489_, v___x_3463_, v___x_3490_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v___x_3489_);
lean_dec_ref(v_alts_3487_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3502_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3502_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3502_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3497_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3497_, 0, v_toMatcherInfo_3481_);
lean_ctor_set(v___x_3497_, 1, v_matcherName_3482_);
lean_ctor_set(v___x_3497_, 2, v_matcherLevels_3483_);
lean_ctor_set(v___x_3497_, 3, v_params_3484_);
lean_ctor_set(v___x_3497_, 4, v_motive_3485_);
lean_ctor_set(v___x_3497_, 5, v_discrs_3486_);
lean_ctor_set(v___x_3497_, 6, v_a_3493_);
lean_ctor_set(v___x_3497_, 7, v_remaining_3488_);
v___x_3498_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3497_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3498_);
v___x_3500_ = v___x_3495_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v_remaining_3488_);
lean_dec_ref(v_discrs_3486_);
lean_dec_ref(v_motive_3485_);
lean_dec_ref(v_params_3484_);
lean_dec_ref(v_matcherLevels_3483_);
lean_dec(v_matcherName_3482_);
lean_dec_ref(v_toMatcherInfo_3481_);
v_a_3503_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3492_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3492_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_toCold_3511_; lean_object* v_inheritedTraceOptions_3512_; lean_object* v___x_3513_; 
lean_dec(v_a_3479_);
lean_dec(v_a_3383_);
v_toCold_3511_ = lean_ctor_get(v___y_3476_, 0);
v_inheritedTraceOptions_3512_ = lean_ctor_get(v_toCold_3511_, 11);
v___x_3513_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3471_, v_inheritedTraceOptions_3512_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; uint8_t v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = lean_unbox(v_a_3514_);
lean_dec(v_a_3514_);
if (v___x_3515_ == 0)
{
v_e_3370_ = v_e_3362_;
v___y_3371_ = v___y_3473_;
v___y_3372_ = v___y_3474_;
v___y_3373_ = v___y_3475_;
v___y_3374_ = v___y_3476_;
v___y_3375_ = v___y_3477_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3517_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3471_, v___x_3516_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_dec_ref_known(v___x_3517_, 1);
v_e_3370_ = v_e_3362_;
v___y_3371_ = v___y_3473_;
v___y_3372_ = v___y_3474_;
v___y_3373_ = v___y_3475_;
v___y_3374_ = v___y_3476_;
v___y_3375_ = v___y_3477_;
goto v___jp_3369_;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v___y_3476_);
lean_dec_ref_known(v_e_3362_, 2);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v___y_3476_);
lean_dec_ref_known(v_e_3362_, 2);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
v_a_3526_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3513_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3513_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec_ref(v___y_3476_);
lean_dec_ref_known(v_e_3362_, 2);
lean_dec(v_a_3383_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
v_a_3534_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3478_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3478_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
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
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref_known(v_e_3362_, 2);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
v_a_3571_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3460_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3460_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
default: 
{
lean_object* v___x_3579_; 
lean_dec(v_a_3383_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
lean_inc_ref(v_e_3362_);
v___x_3579_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3359_, v_e_3362_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec_ref(v_a_3366_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v___x_3579_, 0);
lean_dec(v_unused_3587_);
v___x_3581_ = v___x_3579_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v___x_3579_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v_e_3362_);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_e_3362_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v_e_3362_);
v_a_3588_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3579_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3579_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
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
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_e_3362_);
lean_dec_ref(v_below_3361_);
lean_dec_ref(v_containsRecFn_3360_);
lean_dec_ref(v_recFnNames_3359_);
lean_dec_ref(v_positions_3358_);
lean_dec_ref(v_recArgInfos_3357_);
v_a_3597_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3382_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3382_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
v___jp_3369_:
{
lean_object* v_dummy_3376_; lean_object* v_nargs_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_dummy_3376_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3377_ = l_Lean_Expr_getAppNumArgs(v_e_3370_);
lean_inc(v_nargs_3377_);
v___x_3378_ = lean_mk_array(v_nargs_3377_, v_dummy_3376_);
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = lean_nat_sub(v_nargs_3377_, v___x_3379_);
lean_dec(v_nargs_3377_);
lean_inc_ref(v_e_3370_);
v___x_3381_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3357_, v_positions_3358_, v_recFnNames_3359_, v_containsRecFn_3360_, v_below_3361_, v_e_3370_, v_e_3370_, v___x_3378_, v___x_3380_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec_ref(v___y_3374_);
return v___x_3381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3605_, lean_object* v_recArgInfos_3606_, lean_object* v_positions_3607_, lean_object* v_recFnNames_3608_, lean_object* v_containsRecFn_3609_, lean_object* v_below_3610_, lean_object* v_x_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = lean_expr_instantiate1(v_body_3605_, v_x_3611_);
lean_inc_ref(v___y_3615_);
v___x_3619_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3606_, v_positions_3607_, v_recFnNames_3608_, v_containsRecFn_3609_, v_below_3610_, v___x_3618_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3620_, lean_object* v_positions_3621_, lean_object* v_recFnNames_3622_, lean_object* v_containsRecFn_3623_, lean_object* v_below_3624_, lean_object* v_sz_3625_, lean_object* v_i_3626_, lean_object* v_bs_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
size_t v_sz_boxed_3634_; size_t v_i_boxed_3635_; lean_object* v_res_3636_; 
v_sz_boxed_3634_ = lean_unbox_usize(v_sz_3625_);
lean_dec(v_sz_3625_);
v_i_boxed_3635_ = lean_unbox_usize(v_i_3626_);
lean_dec(v_i_3626_);
v_res_3636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3620_, v_positions_3621_, v_recFnNames_3622_, v_containsRecFn_3623_, v_below_3624_, v_sz_boxed_3634_, v_i_boxed_3635_, v_bs_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3637_, lean_object* v_positions_3638_, lean_object* v_recFnNames_3639_, lean_object* v_containsRecFn_3640_, lean_object* v_a_3641_, lean_object* v_e_3642_, lean_object* v_as_3643_, lean_object* v_bs_3644_, lean_object* v_i_3645_, lean_object* v_cs_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
uint8_t v_a_28525__boxed_3653_; lean_object* v_res_3654_; 
v_a_28525__boxed_3653_ = lean_unbox(v_a_3641_);
v_res_3654_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3637_, v_positions_3638_, v_recFnNames_3639_, v_containsRecFn_3640_, v_a_28525__boxed_3653_, v_e_3642_, v_as_3643_, v_bs_3644_, v_i_3645_, v_cs_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v_bs_3644_);
lean_dec_ref(v_as_3643_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3655_, lean_object* v_positions_3656_, lean_object* v_recFnNames_3657_, lean_object* v_containsRecFn_3658_, lean_object* v_below_3659_, lean_object* v_e_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_, lean_object* v_x_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3655_, v_positions_3656_, v_recFnNames_3657_, v_containsRecFn_3658_, v_below_3659_, v_e_3660_, v_x_3661_, v_x_3662_, v_x_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3671_, lean_object* v_positions_3672_, lean_object* v_recFnNames_3673_, lean_object* v_containsRecFn_3674_, lean_object* v_below_3675_, lean_object* v_e_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3671_, v_positions_3672_, v_recFnNames_3673_, v_containsRecFn_3674_, v_below_3675_, v_e_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
lean_dec(v_a_3681_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
lean_dec(v_a_3677_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3684_, lean_object* v_msg_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3685_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3693_, lean_object* v_msg_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3693_, v_msg_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3702_, lean_object* v_name_3703_, lean_object* v_type_3704_, lean_object* v_val_3705_, lean_object* v_k_3706_, uint8_t v_nondep_3707_, uint8_t v_kind_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3703_, v_type_3704_, v_val_3705_, v_k_3706_, v_nondep_3707_, v_kind_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3716_, lean_object* v_name_3717_, lean_object* v_type_3718_, lean_object* v_val_3719_, lean_object* v_k_3720_, lean_object* v_nondep_3721_, lean_object* v_kind_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
uint8_t v_nondep_boxed_3729_; uint8_t v_kind_boxed_3730_; lean_object* v_res_3731_; 
v_nondep_boxed_3729_ = lean_unbox(v_nondep_3721_);
v_kind_boxed_3730_ = lean_unbox(v_kind_3722_);
v_res_3731_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3716_, v_name_3717_, v_type_3718_, v_val_3719_, v_k_3720_, v_nondep_boxed_3729_, v_kind_boxed_3730_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3732_, v___y_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3748_, lean_object* v_msg_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3748_, v_msg_3749_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3757_, lean_object* v_msg_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3757_, v_msg_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3766_, lean_object* v_constName_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3775_, lean_object* v_constName_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3775_, v_constName_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3784_, lean_object* v_ref_3785_, lean_object* v_constName_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3785_, v_constName_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3794_, lean_object* v_ref_3795_, lean_object* v_constName_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3794_, v_ref_3795_, v_constName_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec(v_ref_3795_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3804_, lean_object* v_ref_3805_, lean_object* v_msg_3806_, lean_object* v_declHint_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3805_, v_msg_3806_, v_declHint_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3815_, lean_object* v_ref_3816_, lean_object* v_msg_3817_, lean_object* v_declHint_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3815_, v_ref_3816_, v_msg_3817_, v_declHint_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec(v_ref_3816_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3826_, lean_object* v_declHint_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3826_, v_declHint_3827_, v___y_3832_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3835_, lean_object* v_declHint_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3835_, v_declHint_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3844_, lean_object* v_ref_3845_, lean_object* v_msg_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3845_, v_msg_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3854_, lean_object* v_ref_3855_, lean_object* v_msg_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3854_, v_ref_3855_, v_msg_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec(v_ref_3855_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3864_, lean_object* v_e_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v_fst_3874_; lean_object* v_snd_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3872_ = lean_st_ref_take(v___y_3866_);
v___x_3873_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3864_, v_e_3865_, v___x_3872_);
v_fst_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_fst_3874_);
v_snd_3875_ = lean_ctor_get(v___x_3873_, 1);
lean_inc(v_snd_3875_);
lean_dec_ref(v___x_3873_);
v___x_3876_ = lean_st_ref_put(v___y_3866_, v_snd_3875_);
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v_fst_3874_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3878_, lean_object* v_e_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3878_, v_e_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v_recFnNames_3878_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3887_, size_t v_i_3888_, lean_object* v_bs_3889_){
_start:
{
uint8_t v___x_3890_; 
v___x_3890_ = lean_usize_dec_lt(v_i_3888_, v_sz_3887_);
if (v___x_3890_ == 0)
{
return v_bs_3889_;
}
else
{
lean_object* v_v_3891_; lean_object* v_fnName_3892_; lean_object* v___x_3893_; lean_object* v_bs_x27_3894_; size_t v___x_3895_; size_t v___x_3896_; lean_object* v___x_3897_; 
v_v_3891_ = lean_array_uget_borrowed(v_bs_3889_, v_i_3888_);
v_fnName_3892_ = lean_ctor_get(v_v_3891_, 0);
lean_inc(v_fnName_3892_);
v___x_3893_ = lean_unsigned_to_nat(0u);
v_bs_x27_3894_ = lean_array_uset(v_bs_3889_, v_i_3888_, v___x_3893_);
v___x_3895_ = ((size_t)1ULL);
v___x_3896_ = lean_usize_add(v_i_3888_, v___x_3895_);
v___x_3897_ = lean_array_uset(v_bs_x27_3894_, v_i_3888_, v_fnName_3892_);
v_i_3888_ = v___x_3896_;
v_bs_3889_ = v___x_3897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3899_, lean_object* v_i_3900_, lean_object* v_bs_3901_){
_start:
{
size_t v_sz_boxed_3902_; size_t v_i_boxed_3903_; lean_object* v_res_3904_; 
v_sz_boxed_3902_ = lean_unbox_usize(v_sz_3899_);
lean_dec(v_sz_3899_);
v_i_boxed_3903_ = lean_unbox_usize(v_i_3900_);
lean_dec(v_i_3900_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3902_, v_i_boxed_3903_, v_bs_3901_);
return v_res_3904_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = lean_box(0);
v___x_3906_ = lean_unsigned_to_nat(16u);
v___x_3907_ = lean_mk_array(v___x_3906_, v___x_3905_);
return v___x_3907_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3908_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3909_ = lean_unsigned_to_nat(0u);
v___x_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
lean_ctor_set(v___x_3910_, 1, v___x_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3911_, lean_object* v_positions_3912_, lean_object* v_below_3913_, lean_object* v_e_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
size_t v_sz_3920_; size_t v___x_3921_; lean_object* v_recFnNames_3922_; lean_object* v_containsRecFn_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_sz_3920_ = lean_array_size(v_recArgInfos_3911_);
v___x_3921_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3911_);
v_recFnNames_3922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3920_, v___x_3921_, v_recArgInfos_3911_);
lean_inc_ref(v_recFnNames_3922_);
v_containsRecFn_3923_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_3923_, 0, v_recFnNames_3922_);
v___x_3924_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3925_ = lean_st_mk_ref(v___x_3924_);
lean_inc_ref(v_a_3917_);
v___x_3926_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3911_, v_positions_3912_, v_recFnNames_3922_, v_containsRecFn_3923_, v_below_3913_, v_e_3914_, v___x_3925_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3935_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3929_ = v___x_3926_;
v_isShared_3930_ = v_isSharedCheck_3935_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3926_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3935_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3931_ = lean_st_ref_get(v___x_3925_);
lean_dec(v___x_3925_);
lean_dec(v___x_3931_);
if (v_isShared_3930_ == 0)
{
v___x_3933_ = v___x_3929_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3927_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
else
{
lean_dec(v___x_3925_);
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_3936_, lean_object* v_positions_3937_, lean_object* v_below_3938_, lean_object* v_e_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_3936_, v_positions_3937_, v_below_3938_, v_e_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_3946_, lean_object* v_k_3947_, uint8_t v_cleanupAnnotations_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v___f_3954_; uint8_t v___x_3955_; uint8_t v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___f_3954_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3954_, 0, v_k_3947_);
v___x_3955_ = 1;
v___x_3956_ = 0;
v___x_3957_ = lean_box(0);
v___x_3958_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3946_, v___x_3955_, v___x_3956_, v___x_3955_, v___x_3956_, v___x_3957_, v___f_3954_, v_cleanupAnnotations_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3958_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3958_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
v_a_3967_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3958_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3958_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_3975_, lean_object* v_k_3976_, lean_object* v_cleanupAnnotations_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3983_; lean_object* v_res_3984_; 
v_cleanupAnnotations_boxed_3983_ = lean_unbox(v_cleanupAnnotations_3977_);
v_res_3984_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_3975_, v_k_3976_, v_cleanupAnnotations_boxed_3983_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_3985_, lean_object* v_e_3986_, lean_object* v_k_3987_, uint8_t v_cleanupAnnotations_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_3986_, v_k_3987_, v_cleanupAnnotations_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_3995_, lean_object* v_e_3996_, lean_object* v_k_3997_, lean_object* v_cleanupAnnotations_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4004_; lean_object* v_res_4005_; 
v_cleanupAnnotations_boxed_4004_ = lean_unbox(v_cleanupAnnotations_3998_);
v_res_4005_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_3995_, v_e_3996_, v_k_3997_, v_cleanupAnnotations_boxed_4004_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4006_, lean_object* v_recArgInfo_4007_, lean_object* v_xs_4008_, lean_object* v___value_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_Meta_instantiateForall(v_type_4006_, v_xs_4008_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4017_; lean_object* v_fst_4018_; lean_object* v_snd_4019_; uint8_t v___x_4020_; uint8_t v___x_4021_; uint8_t v___x_4022_; lean_object* v___x_4023_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
v___x_4017_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4007_, v_xs_4008_);
v_fst_4018_ = lean_ctor_get(v___x_4017_, 0);
lean_inc(v_fst_4018_);
v_snd_4019_ = lean_ctor_get(v___x_4017_, 1);
lean_inc(v_snd_4019_);
lean_dec_ref(v___x_4017_);
v___x_4020_ = 0;
v___x_4021_ = 1;
v___x_4022_ = 1;
v___x_4023_ = l_Lean_Meta_mkForallFVars(v_snd_4019_, v_a_4016_, v___x_4020_, v___x_4021_, v___x_4021_, v___x_4022_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v_snd_4019_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
v___x_4025_ = l_Lean_Meta_mkLambdaFVars(v_fst_4018_, v_a_4024_, v___x_4020_, v___x_4021_, v___x_4020_, v___x_4021_, v___x_4022_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v_fst_4018_);
return v___x_4025_;
}
else
{
lean_dec(v_fst_4018_);
return v___x_4023_;
}
}
else
{
lean_dec_ref(v_xs_4008_);
lean_dec_ref(v_recArgInfo_4007_);
return v___x_4015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4026_, lean_object* v_recArgInfo_4027_, lean_object* v_xs_4028_, lean_object* v___value_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4026_, v_recArgInfo_4027_, v_xs_4028_, v___value_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec_ref(v___value_4029_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4036_, lean_object* v_value_4037_, lean_object* v_type_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v___f_4044_; uint8_t v___x_4045_; lean_object* v___x_4046_; 
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4044_, 0, v_type_4038_);
lean_closure_set(v___f_4044_, 1, v_recArgInfo_4036_);
v___x_4045_ = 0;
v___x_4046_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4037_, v___f_4044_, v___x_4045_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4047_, lean_object* v_value_4048_, lean_object* v_type_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4047_, v_value_4048_, v_type_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4056_, lean_object* v_maxFVars_x3f_4057_, lean_object* v_k_4058_, uint8_t v_cleanupAnnotations_4059_, uint8_t v_whnfType_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v___f_4066_; lean_object* v___x_4067_; 
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4066_, 0, v_k_4058_);
v___x_4067_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4056_, v_maxFVars_x3f_4057_, v___f_4066_, v_cleanupAnnotations_4059_, v_whnfType_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4067_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4067_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
v_a_4076_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4067_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4067_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4084_, lean_object* v_maxFVars_x3f_4085_, lean_object* v_k_4086_, lean_object* v_cleanupAnnotations_4087_, lean_object* v_whnfType_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4094_; uint8_t v_whnfType_boxed_4095_; lean_object* v_res_4096_; 
v_cleanupAnnotations_boxed_4094_ = lean_unbox(v_cleanupAnnotations_4087_);
v_whnfType_boxed_4095_ = lean_unbox(v_whnfType_4088_);
v_res_4096_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4084_, v_maxFVars_x3f_4085_, v_k_4086_, v_cleanupAnnotations_boxed_4094_, v_whnfType_boxed_4095_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4097_, lean_object* v_type_4098_, lean_object* v_maxFVars_x3f_4099_, lean_object* v_k_4100_, uint8_t v_cleanupAnnotations_4101_, uint8_t v_whnfType_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4098_, v_maxFVars_x3f_4099_, v_k_4100_, v_cleanupAnnotations_4101_, v_whnfType_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4109_, lean_object* v_type_4110_, lean_object* v_maxFVars_x3f_4111_, lean_object* v_k_4112_, lean_object* v_cleanupAnnotations_4113_, lean_object* v_whnfType_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4120_; uint8_t v_whnfType_boxed_4121_; lean_object* v_res_4122_; 
v_cleanupAnnotations_boxed_4120_ = lean_unbox(v_cleanupAnnotations_4113_);
v_whnfType_boxed_4121_ = lean_unbox(v_whnfType_4114_);
v_res_4122_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4109_, v_type_4110_, v_maxFVars_x3f_4111_, v_k_4112_, v_cleanupAnnotations_boxed_4120_, v_whnfType_boxed_4121_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4123_, lean_object* v_recArgInfos_4124_, lean_object* v_positions_4125_, lean_object* v_value_4126_, lean_object* v_fst_4127_, lean_object* v_snd_4128_, lean_object* v_below_4129_, lean_object* v_x_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4136_ = lean_unsigned_to_nat(0u);
v___x_4137_ = lean_array_get_borrowed(v___x_4123_, v_below_4129_, v___x_4136_);
lean_inc(v___x_4137_);
v___x_4138_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4124_, v_positions_4125_, v___x_4137_, v_value_4126_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; uint8_t v___x_4145_; uint8_t v___x_4146_; uint8_t v___x_4147_; lean_object* v___x_4148_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4140_ = lean_unsigned_to_nat(1u);
v___x_4141_ = lean_mk_empty_array_with_capacity(v___x_4140_);
lean_inc(v___x_4137_);
v___x_4142_ = lean_array_push(v___x_4141_, v___x_4137_);
v___x_4143_ = l_Array_append___redArg(v_fst_4127_, v___x_4142_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = l_Array_append___redArg(v___x_4143_, v_snd_4128_);
v___x_4145_ = 0;
v___x_4146_ = 1;
v___x_4147_ = 1;
v___x_4148_ = l_Lean_Meta_mkLambdaFVars(v___x_4144_, v_a_4139_, v___x_4145_, v___x_4146_, v___x_4145_, v___x_4146_, v___x_4147_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec_ref(v___x_4144_);
return v___x_4148_;
}
else
{
lean_dec_ref(v_fst_4127_);
return v___x_4138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4149_, lean_object* v_recArgInfos_4150_, lean_object* v_positions_4151_, lean_object* v_value_4152_, lean_object* v_fst_4153_, lean_object* v_snd_4154_, lean_object* v_below_4155_, lean_object* v_x_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4149_, v_recArgInfos_4150_, v_positions_4151_, v_value_4152_, v_fst_4153_, v_snd_4154_, v_below_4155_, v_x_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec_ref(v_x_4156_);
lean_dec_ref(v_below_4155_);
lean_dec_ref(v_snd_4154_);
lean_dec_ref(v___x_4149_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4165_, lean_object* v___x_4166_, lean_object* v_recArgInfos_4167_, lean_object* v_positions_4168_, lean_object* v_FType_4169_, lean_object* v_xs_4170_, lean_object* v_value_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v___x_4177_; lean_object* v_fst_4178_; lean_object* v_snd_4179_; lean_object* v___f_4180_; lean_object* v___x_4181_; 
v___x_4177_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4165_, v_xs_4170_);
v_fst_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc_n(v_fst_4178_, 2);
v_snd_4179_ = lean_ctor_get(v___x_4177_, 1);
lean_inc(v_snd_4179_);
lean_dec_ref(v___x_4177_);
v___f_4180_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4180_, 0, v___x_4166_);
lean_closure_set(v___f_4180_, 1, v_recArgInfos_4167_);
lean_closure_set(v___f_4180_, 2, v_positions_4168_);
lean_closure_set(v___f_4180_, 3, v_value_4171_);
lean_closure_set(v___f_4180_, 4, v_fst_4178_);
lean_closure_set(v___f_4180_, 5, v_snd_4179_);
v___x_4181_ = l_Lean_Meta_instantiateForall(v_FType_4169_, v_fst_4178_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v_fst_4178_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; lean_object* v___x_4185_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4181_, 1);
v___x_4183_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4184_ = 0;
v___x_4185_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4182_, v___x_4183_, v___f_4180_, v___x_4184_, v___x_4184_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
return v___x_4185_;
}
else
{
lean_dec_ref(v___f_4180_);
return v___x_4181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4186_, lean_object* v___x_4187_, lean_object* v_recArgInfos_4188_, lean_object* v_positions_4189_, lean_object* v_FType_4190_, lean_object* v_xs_4191_, lean_object* v_value_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4186_, v___x_4187_, v_recArgInfos_4188_, v_positions_4189_, v_FType_4190_, v_xs_4191_, v_value_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4199_, lean_object* v_positions_4200_, lean_object* v_recArgInfo_4201_, lean_object* v_value_4202_, lean_object* v_FType_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v___x_4209_; lean_object* v___f_4210_; uint8_t v___x_4211_; lean_object* v___x_4212_; 
v___x_4209_ = l_Lean_instInhabitedExpr;
v___f_4210_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4210_, 0, v_recArgInfo_4201_);
lean_closure_set(v___f_4210_, 1, v___x_4209_);
lean_closure_set(v___f_4210_, 2, v_recArgInfos_4199_);
lean_closure_set(v___f_4210_, 3, v_positions_4200_);
lean_closure_set(v___f_4210_, 4, v_FType_4203_);
v___x_4211_ = 0;
v___x_4212_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4202_, v___f_4210_, v___x_4211_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4213_, lean_object* v_positions_4214_, lean_object* v_recArgInfo_4215_, lean_object* v_value_4216_, lean_object* v_FType_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4213_, v_positions_4214_, v_recArgInfo_4215_, v_value_4216_, v_FType_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
lean_dec(v_a_4221_);
lean_dec_ref(v_a_4220_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4224_, lean_object* v_params_4225_, uint8_t v_isIndPred_4226_, lean_object* v_brecOnUniv_4227_, lean_object* v_levels_4228_, lean_object* v_idx_4229_){
_start:
{
lean_object* v_n_4230_; lean_object* v___y_4232_; 
v_n_4230_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4224_, v_idx_4229_);
if (v_isIndPred_4226_ == 0)
{
lean_object* v___x_4235_; 
v___x_4235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4235_, 0, v_brecOnUniv_4227_);
lean_ctor_set(v___x_4235_, 1, v_levels_4228_);
v___y_4232_ = v___x_4235_;
goto v___jp_4231_;
}
else
{
lean_dec(v_brecOnUniv_4227_);
v___y_4232_ = v_levels_4228_;
goto v___jp_4231_;
}
v___jp_4231_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = l_Lean_Expr_const___override(v_n_4230_, v___y_4232_);
v___x_4234_ = l_Lean_mkAppN(v___x_4233_, v_params_4225_);
return v___x_4234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4236_, lean_object* v_params_4237_, lean_object* v_isIndPred_4238_, lean_object* v_brecOnUniv_4239_, lean_object* v_levels_4240_, lean_object* v_idx_4241_){
_start:
{
uint8_t v_isIndPred_boxed_4242_; lean_object* v_res_4243_; 
v_isIndPred_boxed_4242_ = lean_unbox(v_isIndPred_4238_);
v_res_4243_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4236_, v_params_4237_, v_isIndPred_boxed_4242_, v_brecOnUniv_4239_, v_levels_4240_, v_idx_4241_);
lean_dec(v_idx_4241_);
lean_dec_ref(v_params_4237_);
lean_dec_ref(v_toIndGroupInfo_4236_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4244_, lean_object* v_a_4245_, lean_object* v_n_4246_){
_start:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4247_ = lean_apply_1(v_brecOnCons_4244_, v_n_4246_);
v___x_4248_ = l_Lean_mkAppN(v___x_4247_, v_a_4245_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4249_, lean_object* v_a_4250_, lean_object* v_n_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4249_, v_a_4250_, v_n_4251_);
lean_dec_ref(v_a_4250_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4253_, lean_object* v_type_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Lean_Meta_getLevel(v_type_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4261_, lean_object* v_type_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4261_, v_type_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v_x_4261_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4269_, size_t v_sz_4270_, size_t v_i_4271_, lean_object* v_bs_4272_){
_start:
{
uint8_t v___x_4273_; 
v___x_4273_ = lean_usize_dec_lt(v_i_4271_, v_sz_4270_);
if (v___x_4273_ == 0)
{
return v_bs_4272_;
}
else
{
lean_object* v___x_4274_; lean_object* v_v_4275_; lean_object* v___x_4276_; lean_object* v_bs_x27_4277_; lean_object* v___x_4278_; size_t v___x_4279_; size_t v___x_4280_; lean_object* v___x_4281_; 
v___x_4274_ = l_Lean_instInhabitedExpr;
v_v_4275_ = lean_array_uget(v_bs_4272_, v_i_4271_);
v___x_4276_ = lean_unsigned_to_nat(0u);
v_bs_x27_4277_ = lean_array_uset(v_bs_4272_, v_i_4271_, v___x_4276_);
v___x_4278_ = lean_array_get_borrowed(v___x_4274_, v_xs_4269_, v_v_4275_);
lean_dec(v_v_4275_);
v___x_4279_ = ((size_t)1ULL);
v___x_4280_ = lean_usize_add(v_i_4271_, v___x_4279_);
lean_inc(v___x_4278_);
v___x_4281_ = lean_array_uset(v_bs_x27_4277_, v_i_4271_, v___x_4278_);
v_i_4271_ = v___x_4280_;
v_bs_4272_ = v___x_4281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4283_, lean_object* v_sz_4284_, lean_object* v_i_4285_, lean_object* v_bs_4286_){
_start:
{
size_t v_sz_boxed_4287_; size_t v_i_boxed_4288_; lean_object* v_res_4289_; 
v_sz_boxed_4287_ = lean_unbox_usize(v_sz_4284_);
lean_dec(v_sz_4284_);
v_i_boxed_4288_ = lean_unbox_usize(v_i_4285_);
lean_dec(v_i_4285_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4283_, v_sz_boxed_4287_, v_i_boxed_4288_, v_bs_4286_);
lean_dec_ref(v_xs_4283_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4290_, lean_object* v_f_4291_, lean_object* v_as_4292_, lean_object* v_bs_4293_, lean_object* v_i_4294_, lean_object* v_cs_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4301_ = lean_array_get_size(v_as_4292_);
v___x_4302_ = lean_nat_dec_lt(v_i_4294_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; 
lean_dec(v_i_4294_);
lean_dec_ref(v_f_4291_);
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_cs_4295_);
return v___x_4303_;
}
else
{
lean_object* v___x_4304_; uint8_t v___x_4305_; 
v___x_4304_ = lean_array_get_size(v_bs_4293_);
v___x_4305_ = lean_nat_dec_lt(v_i_4294_, v___x_4304_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; 
lean_dec(v_i_4294_);
lean_dec_ref(v_f_4291_);
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v_cs_4295_);
return v___x_4306_;
}
else
{
lean_object* v_a_4307_; lean_object* v_b_4308_; size_t v_sz_4309_; size_t v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_a_4307_ = lean_array_fget_borrowed(v_as_4292_, v_i_4294_);
v_b_4308_ = lean_array_fget_borrowed(v_bs_4293_, v_i_4294_);
v_sz_4309_ = lean_array_size(v_b_4308_);
v___x_4310_ = ((size_t)0ULL);
lean_inc(v_b_4308_);
v___x_4311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4290_, v_sz_4309_, v___x_4310_, v_b_4308_);
lean_inc_ref(v_f_4291_);
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
lean_inc(v_a_4307_);
v___x_4312_ = lean_apply_7(v_f_4291_, v_a_4307_, v___x_4311_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
v___x_4314_ = lean_unsigned_to_nat(1u);
v___x_4315_ = lean_nat_add(v_i_4294_, v___x_4314_);
lean_dec(v_i_4294_);
v___x_4316_ = lean_array_push(v_cs_4295_, v_a_4313_);
v_i_4294_ = v___x_4315_;
v_cs_4295_ = v___x_4316_;
goto _start;
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec_ref(v_cs_4295_);
lean_dec(v_i_4294_);
lean_dec_ref(v_f_4291_);
v_a_4318_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4312_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4312_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4326_, lean_object* v_f_4327_, lean_object* v_as_4328_, lean_object* v_bs_4329_, lean_object* v_i_4330_, lean_object* v_cs_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4326_, v_f_4327_, v_as_4328_, v_bs_4329_, v_i_4330_, v_cs_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec_ref(v_bs_4329_);
lean_dec_ref(v_as_4328_);
lean_dec_ref(v_xs_4326_);
return v_res_4337_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l_Array_instInhabited___redArg();
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v___x_4345_; lean_object* v_toApplicative_4346_; lean_object* v_toFunctor_4347_; lean_object* v_toSeq_4348_; lean_object* v_toSeqLeft_4349_; lean_object* v_toSeqRight_4350_; lean_object* v___f_4351_; lean_object* v___f_4352_; lean_object* v___f_4353_; lean_object* v___f_4354_; lean_object* v___x_4355_; lean_object* v___f_4356_; lean_object* v___f_4357_; lean_object* v___f_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v_toApplicative_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4393_; 
v___x_4345_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4346_ = lean_ctor_get(v___x_4345_, 0);
v_toFunctor_4347_ = lean_ctor_get(v_toApplicative_4346_, 0);
v_toSeq_4348_ = lean_ctor_get(v_toApplicative_4346_, 2);
v_toSeqLeft_4349_ = lean_ctor_get(v_toApplicative_4346_, 3);
v_toSeqRight_4350_ = lean_ctor_get(v_toApplicative_4346_, 4);
v___f_4351_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4352_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4347_, 2);
v___f_4353_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4353_, 0, v_toFunctor_4347_);
v___f_4354_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4354_, 0, v_toFunctor_4347_);
v___x_4355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___f_4353_);
lean_ctor_set(v___x_4355_, 1, v___f_4354_);
lean_inc(v_toSeqRight_4350_);
v___f_4356_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4356_, 0, v_toSeqRight_4350_);
lean_inc(v_toSeqLeft_4349_);
v___f_4357_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4357_, 0, v_toSeqLeft_4349_);
lean_inc(v_toSeq_4348_);
v___f_4358_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4358_, 0, v_toSeq_4348_);
v___x_4359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4355_);
lean_ctor_set(v___x_4359_, 1, v___f_4351_);
lean_ctor_set(v___x_4359_, 2, v___f_4358_);
lean_ctor_set(v___x_4359_, 3, v___f_4357_);
lean_ctor_set(v___x_4359_, 4, v___f_4356_);
v___x_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
lean_ctor_set(v___x_4360_, 1, v___f_4352_);
v___x_4361_ = l_StateRefT_x27_instMonad___redArg(v___x_4360_);
v_toApplicative_4362_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4393_ == 0)
{
lean_object* v_unused_4394_; 
v_unused_4394_ = lean_ctor_get(v___x_4361_, 1);
lean_dec(v_unused_4394_);
v___x_4364_ = v___x_4361_;
v_isShared_4365_ = v_isSharedCheck_4393_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_toApplicative_4362_);
lean_dec(v___x_4361_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4393_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v_toFunctor_4366_; lean_object* v_toSeq_4367_; lean_object* v_toSeqLeft_4368_; lean_object* v_toSeqRight_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4391_; 
v_toFunctor_4366_ = lean_ctor_get(v_toApplicative_4362_, 0);
v_toSeq_4367_ = lean_ctor_get(v_toApplicative_4362_, 2);
v_toSeqLeft_4368_ = lean_ctor_get(v_toApplicative_4362_, 3);
v_toSeqRight_4369_ = lean_ctor_get(v_toApplicative_4362_, 4);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_toApplicative_4362_);
if (v_isSharedCheck_4391_ == 0)
{
lean_object* v_unused_4392_; 
v_unused_4392_ = lean_ctor_get(v_toApplicative_4362_, 1);
lean_dec(v_unused_4392_);
v___x_4371_ = v_toApplicative_4362_;
v_isShared_4372_ = v_isSharedCheck_4391_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_toSeqRight_4369_);
lean_inc(v_toSeqLeft_4368_);
lean_inc(v_toSeq_4367_);
lean_inc(v_toFunctor_4366_);
lean_dec(v_toApplicative_4362_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4391_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___f_4373_; lean_object* v___f_4374_; lean_object* v___f_4375_; lean_object* v___f_4376_; lean_object* v___x_4377_; lean_object* v___f_4378_; lean_object* v___f_4379_; lean_object* v___f_4380_; lean_object* v___x_4382_; 
v___f_4373_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4374_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4366_);
v___f_4375_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4375_, 0, v_toFunctor_4366_);
v___f_4376_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4376_, 0, v_toFunctor_4366_);
v___x_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___f_4375_);
lean_ctor_set(v___x_4377_, 1, v___f_4376_);
v___f_4378_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4378_, 0, v_toSeqRight_4369_);
v___f_4379_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4379_, 0, v_toSeqLeft_4368_);
v___f_4380_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4380_, 0, v_toSeq_4367_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 4, v___f_4378_);
lean_ctor_set(v___x_4371_, 3, v___f_4379_);
lean_ctor_set(v___x_4371_, 2, v___f_4380_);
lean_ctor_set(v___x_4371_, 1, v___f_4373_);
lean_ctor_set(v___x_4371_, 0, v___x_4377_);
v___x_4382_ = v___x_4371_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4377_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v___f_4373_);
lean_ctor_set(v_reuseFailAlloc_4390_, 2, v___f_4380_);
lean_ctor_set(v_reuseFailAlloc_4390_, 3, v___f_4379_);
lean_ctor_set(v_reuseFailAlloc_4390_, 4, v___f_4378_);
v___x_4382_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4384_; 
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 1, v___f_4374_);
lean_ctor_set(v___x_4364_, 0, v___x_4382_);
v___x_4384_ = v___x_4364_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4382_);
lean_ctor_set(v_reuseFailAlloc_4389_, 1, v___f_4374_);
v___x_4384_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_855__overap_4387_; lean_object* v___x_4388_; 
v___x_4385_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4386_ = l_instInhabitedOfMonad___redArg(v___x_4384_, v___x_4385_);
v___x_855__overap_4387_ = lean_panic_fn_borrowed(v___x_4386_, v_msg_4339_);
lean_dec(v___x_4386_);
lean_inc(v___y_4343_);
lean_inc_ref(v___y_4342_);
lean_inc(v___y_4341_);
lean_inc_ref(v___y_4340_);
v___x_4388_ = lean_apply_5(v___x_855__overap_4387_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, lean_box(0));
return v___x_4388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
return v_res_4401_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4405_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4406_ = lean_unsigned_to_nat(2u);
v___x_4407_ = lean_unsigned_to_nat(73u);
v___x_4408_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4409_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4410_ = l_mkPanicMessageWithDecl(v___x_4409_, v___x_4408_, v___x_4407_, v___x_4406_, v___x_4405_);
return v___x_4410_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4412_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4413_ = lean_unsigned_to_nat(2u);
v___x_4414_ = lean_unsigned_to_nat(74u);
v___x_4415_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4416_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4417_ = l_mkPanicMessageWithDecl(v___x_4416_, v___x_4415_, v___x_4414_, v___x_4413_, v___x_4412_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4420_, lean_object* v_positions_4421_, lean_object* v_ys_4422_, lean_object* v_xs_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; 
v___x_4429_ = lean_array_get_size(v_positions_4421_);
v___x_4430_ = lean_array_get_size(v_ys_4422_);
v___x_4431_ = lean_nat_dec_eq(v___x_4429_, v___x_4430_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
lean_dec_ref(v_f_4420_);
v___x_4432_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4433_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4432_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
return v___x_4433_;
}
else
{
lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v___x_4434_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4421_);
v___x_4435_ = lean_array_get_size(v_xs_4423_);
v___x_4436_ = lean_nat_dec_eq(v___x_4434_, v___x_4435_);
lean_dec(v___x_4434_);
if (v___x_4436_ == 0)
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
lean_dec_ref(v_f_4420_);
v___x_4437_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4438_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4437_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
return v___x_4438_;
}
else
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4439_ = lean_unsigned_to_nat(0u);
v___x_4440_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4441_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4423_, v_f_4420_, v_ys_4422_, v_positions_4421_, v___x_4439_, v___x_4440_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
return v___x_4441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4442_, lean_object* v_positions_4443_, lean_object* v_ys_4444_, lean_object* v_xs_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4442_, v_positions_4443_, v_ys_4444_, v_xs_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec_ref(v_xs_4445_);
lean_dec_ref(v_ys_4444_);
lean_dec_ref(v_positions_4443_);
return v_res_4451_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = lean_unsigned_to_nat(0u);
v___x_4454_ = l_Lean_Level_ofNat(v___x_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4455_, lean_object* v_positions_4456_, lean_object* v_motives_4457_, uint8_t v_isIndPred_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v_indGroupInst_4467_; lean_object* v_brecOnUniv_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; 
v___x_4464_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4465_ = lean_unsigned_to_nat(0u);
v___x_4466_ = lean_array_get_borrowed(v___x_4464_, v_recArgInfos_4455_, v___x_4465_);
v_indGroupInst_4467_ = lean_ctor_get(v___x_4466_, 4);
if (v_isIndPred_4458_ == 0)
{
lean_object* v___f_4510_; lean_object* v___x_4511_; lean_object* v_motive_4512_; lean_object* v___x_4513_; 
v___f_4510_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4511_ = l_Lean_instInhabitedExpr;
v_motive_4512_ = lean_array_get_borrowed(v___x_4511_, v_motives_4457_, v___x_4465_);
lean_inc(v_motive_4512_);
v___x_4513_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4512_, v___f_4510_, v_isIndPred_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4513_, 1);
v_brecOnUniv_4469_ = v_a_4514_;
v___y_4470_ = v_a_4459_;
v___y_4471_ = v_a_4460_;
v___y_4472_ = v_a_4461_;
v___y_4473_ = v_a_4462_;
goto v___jp_4468_;
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
v_a_4515_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4513_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4513_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
else
{
lean_object* v___x_4523_; 
v___x_4523_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4469_ = v___x_4523_;
v___y_4470_ = v_a_4459_;
v___y_4471_ = v_a_4460_;
v___y_4472_ = v_a_4461_;
v___y_4473_ = v_a_4462_;
goto v___jp_4468_;
}
v___jp_4468_:
{
lean_object* v_toIndGroupInfo_4474_; lean_object* v_levels_4475_; lean_object* v_params_4476_; lean_object* v___x_4477_; lean_object* v_brecOnCons_4478_; lean_object* v_brecOnAux_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v_toIndGroupInfo_4474_ = lean_ctor_get(v_indGroupInst_4467_, 0);
v_levels_4475_ = lean_ctor_get(v_indGroupInst_4467_, 1);
v_params_4476_ = lean_ctor_get(v_indGroupInst_4467_, 2);
v___x_4477_ = lean_box(v_isIndPred_4458_);
lean_inc_n(v_levels_4475_, 2);
lean_inc(v_brecOnUniv_4469_);
lean_inc_ref(v_params_4476_);
lean_inc_ref(v_toIndGroupInfo_4474_);
v_brecOnCons_4478_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4478_, 0, v_toIndGroupInfo_4474_);
lean_closure_set(v_brecOnCons_4478_, 1, v_params_4476_);
lean_closure_set(v_brecOnCons_4478_, 2, v___x_4477_);
lean_closure_set(v_brecOnCons_4478_, 3, v_brecOnUniv_4469_);
lean_closure_set(v_brecOnCons_4478_, 4, v_levels_4475_);
v_brecOnAux_4479_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4474_, v_params_4476_, v_isIndPred_4458_, v_brecOnUniv_4469_, v_levels_4475_, v___x_4465_);
v___x_4480_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4474_);
v___x_4481_ = l_Lean_Meta_inferArgumentTypesN(v___x_4480_, v_brecOnAux_4479_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
v___x_4483_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4484_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4483_, v_positions_4456_, v_a_4482_, v_motives_4457_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
lean_dec(v_a_4482_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4493_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4493_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4493_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___f_4489_; lean_object* v___x_4491_; 
v___f_4489_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4489_, 0, v_brecOnCons_4478_);
lean_closure_set(v___f_4489_, 1, v_a_4485_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___f_4489_);
v___x_4491_ = v___x_4487_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___f_4489_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec_ref(v_brecOnCons_4478_);
v_a_4494_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4484_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4484_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec_ref(v_brecOnCons_4478_);
v_a_4502_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4481_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4481_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4524_, lean_object* v_positions_4525_, lean_object* v_motives_4526_, lean_object* v_isIndPred_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
uint8_t v_isIndPred_boxed_4533_; lean_object* v_res_4534_; 
v_isIndPred_boxed_4533_ = lean_unbox(v_isIndPred_4527_);
v_res_4534_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4524_, v_positions_4525_, v_motives_4526_, v_isIndPred_boxed_4533_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
lean_dec_ref(v_motives_4526_);
lean_dec_ref(v_positions_4525_);
lean_dec_ref(v_recArgInfos_4524_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4535_, lean_object* v_msg_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4543_, lean_object* v_msg_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4543_, v_msg_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4551_, lean_object* v_00_u03b1_4552_, lean_object* v_f_4553_, lean_object* v_positions_4554_, lean_object* v_ys_4555_, lean_object* v_xs_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; 
v___x_4562_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4553_, v_positions_4554_, v_ys_4555_, v_xs_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4563_, lean_object* v_00_u03b1_4564_, lean_object* v_f_4565_, lean_object* v_positions_4566_, lean_object* v_ys_4567_, lean_object* v_xs_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4563_, v_00_u03b1_4564_, v_f_4565_, v_positions_4566_, v_ys_4567_, v_xs_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v_xs_4568_);
lean_dec_ref(v_ys_4567_);
lean_dec_ref(v_positions_4566_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4575_, lean_object* v_00_u03b3_4576_, lean_object* v_xs_4577_, lean_object* v_f_4578_, lean_object* v_as_4579_, lean_object* v_bs_4580_, lean_object* v_i_4581_, lean_object* v_cs_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v___x_4588_; 
v___x_4588_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4577_, v_f_4578_, v_as_4579_, v_bs_4580_, v_i_4581_, v_cs_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4589_, lean_object* v_00_u03b3_4590_, lean_object* v_xs_4591_, lean_object* v_f_4592_, lean_object* v_as_4593_, lean_object* v_bs_4594_, lean_object* v_i_4595_, lean_object* v_cs_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4589_, v_00_u03b3_4590_, v_xs_4591_, v_f_4592_, v_as_4593_, v_bs_4594_, v_i_4595_, v_cs_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec_ref(v_bs_4594_);
lean_dec_ref(v_as_4593_);
lean_dec_ref(v_xs_4591_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v_numTypeFormers_4603_, lean_object* v_x_4604_, lean_object* v_brecOnType_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4611_; 
v___x_4611_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4603_, v_brecOnType_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed(lean_object* v_numTypeFormers_4612_, lean_object* v_x_4613_, lean_object* v_brecOnType_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(v_numTypeFormers_4612_, v_x_4613_, v_brecOnType_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec_ref(v_x_4613_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v___x_4621_, lean_object* v_e_4622_){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = l_Lean_indentD(v_e_4622_);
v___x_4624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4621_);
lean_ctor_set(v___x_4624_, 1, v___x_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4625_, lean_object* v_as_4626_, size_t v_sz_4627_, size_t v_i_4628_, lean_object* v_b_4629_){
_start:
{
uint8_t v___x_4631_; 
v___x_4631_ = lean_usize_dec_lt(v_i_4628_, v_sz_4627_);
if (v___x_4631_ == 0)
{
lean_object* v___x_4632_; 
lean_dec_ref(v_a_4625_);
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v_b_4629_);
return v___x_4632_;
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4634_; size_t v___x_4635_; size_t v___x_4636_; 
v_a_4633_ = lean_array_uget_borrowed(v_as_4626_, v_i_4628_);
lean_inc_ref(v_a_4625_);
v___x_4634_ = lean_array_set(v_b_4629_, v_a_4633_, v_a_4625_);
v___x_4635_ = ((size_t)1ULL);
v___x_4636_ = lean_usize_add(v_i_4628_, v___x_4635_);
v_i_4628_ = v___x_4636_;
v_b_4629_ = v___x_4634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4638_, lean_object* v_as_4639_, lean_object* v_sz_4640_, lean_object* v_i_4641_, lean_object* v_b_4642_, lean_object* v___y_4643_){
_start:
{
size_t v_sz_boxed_4644_; size_t v_i_boxed_4645_; lean_object* v_res_4646_; 
v_sz_boxed_4644_ = lean_unbox_usize(v_sz_4640_);
lean_dec(v_sz_4640_);
v_i_boxed_4645_ = lean_unbox_usize(v_i_4641_);
lean_dec(v_i_4641_);
v_res_4646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4638_, v_as_4639_, v_sz_boxed_4644_, v_i_boxed_4645_, v_b_4642_);
lean_dec_ref(v_as_4639_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4647_, size_t v_sz_4648_, size_t v_i_4649_, lean_object* v_b_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
uint8_t v___x_4656_; 
v___x_4656_ = lean_usize_dec_lt(v_i_4649_, v_sz_4648_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v_b_4650_);
return v___x_4657_;
}
else
{
lean_object* v_snd_4658_; lean_object* v_fst_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4703_; 
v_snd_4658_ = lean_ctor_get(v_b_4650_, 1);
v_fst_4659_ = lean_ctor_get(v_b_4650_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v_b_4650_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4661_ = v_b_4650_;
v_isShared_4662_ = v_isSharedCheck_4703_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_snd_4658_);
lean_inc(v_fst_4659_);
lean_dec(v_b_4650_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4703_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v_array_4663_; lean_object* v_start_4664_; lean_object* v_stop_4665_; uint8_t v___x_4666_; 
v_array_4663_ = lean_ctor_get(v_snd_4658_, 0);
v_start_4664_ = lean_ctor_get(v_snd_4658_, 1);
v_stop_4665_ = lean_ctor_get(v_snd_4658_, 2);
v___x_4666_ = lean_nat_dec_lt(v_start_4664_, v_stop_4665_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4668_; 
if (v_isShared_4662_ == 0)
{
v___x_4668_ = v___x_4661_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_fst_4659_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v_snd_4658_);
v___x_4668_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
lean_object* v___x_4669_; 
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4668_);
return v___x_4669_;
}
}
else
{
lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4699_; 
lean_inc(v_stop_4665_);
lean_inc(v_start_4664_);
lean_inc_ref(v_array_4663_);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_snd_4658_);
if (v_isSharedCheck_4699_ == 0)
{
lean_object* v_unused_4700_; lean_object* v_unused_4701_; lean_object* v_unused_4702_; 
v_unused_4700_ = lean_ctor_get(v_snd_4658_, 2);
lean_dec(v_unused_4700_);
v_unused_4701_ = lean_ctor_get(v_snd_4658_, 1);
lean_dec(v_unused_4701_);
v_unused_4702_ = lean_ctor_get(v_snd_4658_, 0);
lean_dec(v_unused_4702_);
v___x_4672_ = v_snd_4658_;
v_isShared_4673_ = v_isSharedCheck_4699_;
goto v_resetjp_4671_;
}
else
{
lean_dec(v_snd_4658_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4699_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v_a_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
v_a_4674_ = lean_array_uget_borrowed(v_as_4647_, v_i_4649_);
v___x_4675_ = lean_array_fget(v_array_4663_, v_start_4664_);
v___x_4676_ = lean_unsigned_to_nat(1u);
v___x_4677_ = lean_nat_add(v_start_4664_, v___x_4676_);
lean_dec(v_start_4664_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 1, v___x_4677_);
v___x_4679_ = v___x_4672_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_array_4663_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4698_, 2, v_stop_4665_);
v___x_4679_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
size_t v_sz_4680_; size_t v___x_4681_; lean_object* v___x_4682_; 
v_sz_4680_ = lean_array_size(v___x_4675_);
v___x_4681_ = ((size_t)0ULL);
lean_inc(v_a_4674_);
v___x_4682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4674_, v___x_4675_, v_sz_4680_, v___x_4681_, v_fst_4659_);
lean_dec(v___x_4675_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4683_);
lean_dec_ref_known(v___x_4682_, 1);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 1, v___x_4679_);
lean_ctor_set(v___x_4661_, 0, v_a_4683_);
v___x_4685_ = v___x_4661_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v___x_4679_);
v___x_4685_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
size_t v___x_4686_; size_t v___x_4687_; 
v___x_4686_ = ((size_t)1ULL);
v___x_4687_ = lean_usize_add(v_i_4649_, v___x_4686_);
v_i_4649_ = v___x_4687_;
v_b_4650_ = v___x_4685_;
goto _start;
}
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
lean_dec_ref(v___x_4679_);
lean_del_object(v___x_4661_);
v_a_4690_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___x_4682_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4682_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4704_, lean_object* v_sz_4705_, lean_object* v_i_4706_, lean_object* v_b_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
size_t v_sz_boxed_4713_; size_t v_i_boxed_4714_; lean_object* v_res_4715_; 
v_sz_boxed_4713_ = lean_unbox_usize(v_sz_4705_);
lean_dec(v_sz_4705_);
v_i_boxed_4714_ = lean_unbox_usize(v_i_4706_);
lean_dec(v_i_4706_);
v_res_4715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4704_, v_sz_boxed_4713_, v_i_boxed_4714_, v_b_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec_ref(v_as_4704_);
return v_res_4715_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4717_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4718_ = l_Lean_stringToMessageData(v___x_4717_);
return v___x_4718_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4719_; lean_object* v___f_4720_; 
v___x_4719_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4720_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1), 2, 1);
lean_closure_set(v___f_4720_, 0, v___x_4719_);
return v___f_4720_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4722_ = l_Lean_Expr_sort___override(v___x_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4723_, lean_object* v_positions_4724_, lean_object* v_brecOnConst_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v_recArgInfo_4733_; lean_object* v_indicesPos_4734_; lean_object* v_indIdx_4735_; lean_object* v_numTypeFormers_4736_; lean_object* v___f_4737_; lean_object* v_brecOn_4738_; lean_object* v___f_4739_; uint8_t v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4731_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4732_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4733_ = lean_array_get_borrowed(v___x_4731_, v_recArgInfos_4723_, v___x_4732_);
v_indicesPos_4734_ = lean_ctor_get(v_recArgInfo_4733_, 3);
v_indIdx_4735_ = lean_ctor_get(v_recArgInfo_4733_, 5);
v_numTypeFormers_4736_ = lean_array_get_size(v_positions_4724_);
v___f_4737_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4737_, 0, v_numTypeFormers_4736_);
lean_inc(v_indIdx_4735_);
v_brecOn_4738_ = lean_apply_1(v_brecOnConst_4725_, v_indIdx_4735_);
v___f_4739_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4740_ = 0;
v___x_4741_ = lean_box(v___x_4740_);
lean_inc_ref(v_brecOn_4738_);
v___x_4742_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4742_, 0, v_brecOn_4738_);
lean_closure_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4742_, v___f_4739_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v___x_4744_; 
lean_dec_ref_known(v___x_4743_, 1);
lean_inc(v_a_4729_);
lean_inc_ref(v_a_4728_);
lean_inc(v_a_4727_);
lean_inc_ref(v_a_4726_);
v___x_4744_ = lean_infer_type(v_brecOn_4738_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; lean_object* v___x_4751_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
v___x_4746_ = lean_array_get_size(v_indicesPos_4734_);
v___x_4747_ = lean_unsigned_to_nat(1u);
v___x_4748_ = lean_nat_add(v___x_4746_, v___x_4747_);
v___x_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4748_);
v___x_4750_ = 0;
v___x_4751_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4745_, v___x_4749_, v___f_4737_, v___x_4750_, v___x_4750_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; size_t v_sz_4758_; size_t v___x_4759_; lean_object* v___x_4760_; 
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
lean_inc(v_a_4752_);
lean_dec_ref_known(v___x_4751_, 1);
v___x_4753_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4724_);
v___x_4754_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4755_ = lean_mk_array(v___x_4753_, v___x_4754_);
v___x_4756_ = l_Array_toSubarray___redArg(v_positions_4724_, v___x_4732_, v_numTypeFormers_4736_);
v___x_4757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4755_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
v_sz_4758_ = lean_array_size(v_a_4752_);
v___x_4759_ = ((size_t)0ULL);
v___x_4760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4752_, v_sz_4758_, v___x_4759_, v___x_4757_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
lean_dec(v_a_4752_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4769_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4763_ = v___x_4760_;
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4760_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v_fst_4765_; lean_object* v___x_4767_; 
v_fst_4765_ = lean_ctor_get(v_a_4761_, 0);
lean_inc(v_fst_4765_);
lean_dec(v_a_4761_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 0, v_fst_4765_);
v___x_4767_ = v___x_4763_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_fst_4765_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
v_a_4770_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4760_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4760_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4724_);
return v___x_4751_;
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
lean_dec_ref(v___f_4737_);
lean_dec_ref(v_positions_4724_);
v_a_4778_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4744_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4744_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec_ref(v_brecOn_4738_);
lean_dec_ref(v___f_4737_);
lean_dec_ref(v_positions_4724_);
v_a_4786_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4743_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4743_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4794_, lean_object* v_positions_4795_, lean_object* v_brecOnConst_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4794_, v_positions_4795_, v_brecOnConst_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec_ref(v_recArgInfos_4794_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4803_, lean_object* v_as_4804_, size_t v_sz_4805_, size_t v_i_4806_, lean_object* v_b_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4803_, v_as_4804_, v_sz_4805_, v_i_4806_, v_b_4807_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4814_, lean_object* v_as_4815_, lean_object* v_sz_4816_, lean_object* v_i_4817_, lean_object* v_b_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
size_t v_sz_boxed_4824_; size_t v_i_boxed_4825_; lean_object* v_res_4826_; 
v_sz_boxed_4824_ = lean_unbox_usize(v_sz_4816_);
lean_dec(v_sz_4816_);
v_i_boxed_4825_ = lean_unbox_usize(v_i_4817_);
lean_dec(v_i_4817_);
v_res_4826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4814_, v_as_4815_, v_sz_boxed_4824_, v_i_boxed_4825_, v_b_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec_ref(v_as_4815_);
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4827_, lean_object* v_a_4828_){
_start:
{
if (lean_obj_tag(v_a_4827_) == 0)
{
lean_object* v___x_4829_; 
v___x_4829_ = l_List_reverse___redArg(v_a_4828_);
return v___x_4829_;
}
else
{
lean_object* v_head_4830_; lean_object* v_tail_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4842_; 
v_head_4830_ = lean_ctor_get(v_a_4827_, 0);
v_tail_4831_ = lean_ctor_get(v_a_4827_, 1);
v_isSharedCheck_4842_ = !lean_is_exclusive(v_a_4827_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4833_ = v_a_4827_;
v_isShared_4834_ = v_isSharedCheck_4842_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_tail_4831_);
lean_inc(v_head_4830_);
lean_dec(v_a_4827_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4842_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4835_ = l_Nat_reprFast(v_head_4830_);
v___x_4836_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4835_);
v___x_4837_ = l_Lean_MessageData_ofFormat(v___x_4836_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 1, v_a_4828_);
lean_ctor_set(v___x_4833_, 0, v___x_4837_);
v___x_4839_ = v___x_4833_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4837_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v_a_4828_);
v___x_4839_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
v_a_4827_ = v_tail_4831_;
v_a_4828_ = v___x_4839_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4843_, lean_object* v_a_4844_){
_start:
{
if (lean_obj_tag(v_a_4843_) == 0)
{
lean_object* v___x_4845_; 
v___x_4845_ = l_List_reverse___redArg(v_a_4844_);
return v___x_4845_;
}
else
{
lean_object* v_head_4846_; lean_object* v_tail_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4859_; 
v_head_4846_ = lean_ctor_get(v_a_4843_, 0);
v_tail_4847_ = lean_ctor_get(v_a_4843_, 1);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_a_4843_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4849_ = v_a_4843_;
v_isShared_4850_ = v_isSharedCheck_4859_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_tail_4847_);
lean_inc(v_head_4846_);
lean_dec(v_a_4843_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4859_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4856_; 
v___x_4851_ = lean_array_to_list(v_head_4846_);
v___x_4852_ = lean_box(0);
v___x_4853_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4851_, v___x_4852_);
v___x_4854_ = l_Lean_MessageData_ofList(v___x_4853_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v_a_4844_);
lean_ctor_set(v___x_4849_, 0, v___x_4854_);
v___x_4856_ = v___x_4849_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_a_4844_);
v___x_4856_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
v_a_4843_ = v_tail_4847_;
v_a_4844_ = v___x_4856_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4860_, lean_object* v_v_4861_, lean_object* v_i_4862_){
_start:
{
lean_object* v___x_4863_; uint8_t v___x_4864_; 
v___x_4863_ = lean_array_get_size(v_xs_4860_);
v___x_4864_ = lean_nat_dec_lt(v_i_4862_, v___x_4863_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; 
lean_dec(v_i_4862_);
v___x_4865_ = lean_box(0);
return v___x_4865_;
}
else
{
lean_object* v___x_4866_; uint8_t v___x_4867_; 
v___x_4866_ = lean_array_fget_borrowed(v_xs_4860_, v_i_4862_);
v___x_4867_ = lean_nat_dec_eq(v___x_4866_, v_v_4861_);
if (v___x_4867_ == 0)
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = lean_unsigned_to_nat(1u);
v___x_4869_ = lean_nat_add(v_i_4862_, v___x_4868_);
lean_dec(v_i_4862_);
v_i_4862_ = v___x_4869_;
goto _start;
}
else
{
lean_object* v___x_4871_; 
v___x_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4871_, 0, v_i_4862_);
return v___x_4871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4872_, lean_object* v_v_4873_, lean_object* v_i_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4872_, v_v_4873_, v_i_4874_);
lean_dec(v_v_4873_);
lean_dec_ref(v_xs_4872_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4876_, lean_object* v_v_4877_){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = lean_unsigned_to_nat(0u);
v___x_4879_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4876_, v_v_4877_, v___x_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4880_, lean_object* v_v_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4880_, v_v_4881_);
lean_dec(v_v_4881_);
lean_dec_ref(v_xs_4880_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4886_, lean_object* v_as_4887_, size_t v_sz_4888_, size_t v_i_4889_, lean_object* v_b_4890_){
_start:
{
uint8_t v___x_4891_; 
v___x_4891_ = lean_usize_dec_lt(v_i_4889_, v_sz_4888_);
if (v___x_4891_ == 0)
{
lean_inc_ref(v_b_4890_);
return v_b_4890_;
}
else
{
lean_object* v___x_4892_; lean_object* v_a_4893_; lean_object* v___x_4894_; 
v___x_4892_ = lean_box(0);
v_a_4893_ = lean_array_uget_borrowed(v_as_4887_, v_i_4889_);
v___x_4894_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4893_, v_fnIdx_4886_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v___x_4895_; size_t v___x_4896_; size_t v___x_4897_; 
v___x_4895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4896_ = ((size_t)1ULL);
v___x_4897_ = lean_usize_add(v_i_4889_, v___x_4896_);
v_i_4889_ = v___x_4897_;
v_b_4890_ = v___x_4895_;
goto _start;
}
else
{
lean_object* v_val_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4910_; 
v_val_4899_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4901_ = v___x_4894_;
v_isShared_4902_ = v_isSharedCheck_4910_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_val_4899_);
lean_dec(v___x_4894_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4910_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4906_; 
v___x_4903_ = lean_array_get_size(v_a_4893_);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
lean_ctor_set(v___x_4904_, 1, v_val_4899_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4904_);
v___x_4906_ = v___x_4901_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4904_);
v___x_4906_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
v___x_4908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
lean_ctor_set(v___x_4908_, 1, v___x_4892_);
return v___x_4908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4911_, lean_object* v_as_4912_, lean_object* v_sz_4913_, lean_object* v_i_4914_, lean_object* v_b_4915_){
_start:
{
size_t v_sz_boxed_4916_; size_t v_i_boxed_4917_; lean_object* v_res_4918_; 
v_sz_boxed_4916_ = lean_unbox_usize(v_sz_4913_);
lean_dec(v_sz_4913_);
v_i_boxed_4917_ = lean_unbox_usize(v_i_4914_);
lean_dec(v_i_4914_);
v_res_4918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4911_, v_as_4912_, v_sz_boxed_4916_, v_i_boxed_4917_, v_b_4915_);
lean_dec_ref(v_b_4915_);
lean_dec_ref(v_as_4912_);
lean_dec(v_fnIdx_4911_);
return v_res_4918_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4920_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4921_ = l_Lean_stringToMessageData(v___x_4920_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4922_, lean_object* v_positions_4923_, lean_object* v_fnIdx_4924_, lean_object* v_brecOnConst_4925_, lean_object* v_packedFArgs_4926_, lean_object* v_funTypes_4927_, lean_object* v_ys_4928_, lean_object* v___value_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v___x_4949_; lean_object* v_fst_4950_; lean_object* v_snd_4951_; lean_object* v___x_4952_; size_t v_sz_4953_; size_t v___x_4954_; lean_object* v___x_4955_; lean_object* v_fst_4956_; 
lean_inc_ref(v_ys_4928_);
lean_inc_ref(v_recArgInfo_4922_);
v___x_4949_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4922_, v_ys_4928_);
v_fst_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_fst_4950_);
v_snd_4951_ = lean_ctor_get(v___x_4949_, 1);
lean_inc(v_snd_4951_);
lean_dec_ref(v___x_4949_);
v___x_4952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_4953_ = lean_array_size(v_positions_4923_);
v___x_4954_ = ((size_t)0ULL);
v___x_4955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4924_, v_positions_4923_, v_sz_4953_, v___x_4954_, v___x_4952_);
v_fst_4956_ = lean_ctor_get(v___x_4955_, 0);
lean_inc(v_fst_4956_);
lean_dec_ref(v___x_4955_);
if (lean_obj_tag(v_fst_4956_) == 0)
{
lean_dec(v_snd_4951_);
lean_dec(v_fst_4950_);
lean_dec_ref(v_ys_4928_);
lean_dec_ref(v_brecOnConst_4925_);
lean_dec_ref(v_recArgInfo_4922_);
goto v___jp_4935_;
}
else
{
lean_object* v_val_4957_; 
v_val_4957_ = lean_ctor_get(v_fst_4956_, 0);
lean_inc(v_val_4957_);
lean_dec_ref_known(v_fst_4956_, 1);
if (lean_obj_tag(v_val_4957_) == 1)
{
lean_object* v_val_4958_; lean_object* v_fst_4959_; lean_object* v_snd_4960_; lean_object* v_indIdx_4961_; lean_object* v_brecOn_4962_; lean_object* v_brecOn_4963_; lean_object* v_brecOn_4964_; lean_object* v___x_4965_; 
lean_dec(v_fnIdx_4924_);
lean_dec_ref(v_positions_4923_);
v_val_4958_ = lean_ctor_get(v_val_4957_, 0);
lean_inc(v_val_4958_);
lean_dec_ref_known(v_val_4957_, 1);
v_fst_4959_ = lean_ctor_get(v_val_4958_, 0);
lean_inc(v_fst_4959_);
v_snd_4960_ = lean_ctor_get(v_val_4958_, 1);
lean_inc(v_snd_4960_);
lean_dec(v_val_4958_);
v_indIdx_4961_ = lean_ctor_get(v_recArgInfo_4922_, 5);
lean_inc(v_indIdx_4961_);
lean_dec_ref(v_recArgInfo_4922_);
v_brecOn_4962_ = lean_apply_1(v_brecOnConst_4925_, v_indIdx_4961_);
v_brecOn_4963_ = l_Lean_mkAppN(v_brecOn_4962_, v_fst_4950_);
lean_dec(v_fst_4950_);
v_brecOn_4964_ = l_Lean_mkAppN(v_brecOn_4963_, v_packedFArgs_4926_);
v___x_4965_ = l_Lean_Meta_PProdN_projM(v_fst_4959_, v_snd_4960_, v_brecOn_4964_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
lean_dec(v_snd_4960_);
lean_dec(v_fst_4959_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v___x_4967_; uint8_t v___x_4968_; uint8_t v___x_4969_; lean_object* v___x_4970_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4965_, 1);
v___x_4967_ = l_Lean_mkAppN(v_a_4966_, v_snd_4951_);
lean_dec(v_snd_4951_);
v___x_4968_ = 1;
v___x_4969_ = 1;
v___x_4970_ = l_Lean_Meta_mkLetFVars(v_funTypes_4927_, v___x_4967_, v___x_4968_, v___x_4968_, v___x_4969_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; uint8_t v___x_4972_; lean_object* v___x_4973_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
lean_inc(v_a_4971_);
lean_dec_ref_known(v___x_4970_, 1);
v___x_4972_ = 0;
v___x_4973_ = l_Lean_Meta_mkLambdaFVars(v_ys_4928_, v_a_4971_, v___x_4972_, v___x_4968_, v___x_4972_, v___x_4968_, v___x_4969_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
lean_dec_ref(v_ys_4928_);
return v___x_4973_;
}
else
{
lean_dec_ref(v_ys_4928_);
return v___x_4970_;
}
}
else
{
lean_dec(v_snd_4951_);
lean_dec_ref(v_ys_4928_);
return v___x_4965_;
}
}
else
{
lean_dec(v_val_4957_);
lean_dec(v_snd_4951_);
lean_dec(v_fst_4950_);
lean_dec_ref(v_ys_4928_);
lean_dec_ref(v_brecOnConst_4925_);
lean_dec_ref(v_recArgInfo_4922_);
goto v___jp_4935_;
}
}
v___jp_4935_:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4936_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_4937_ = l_Nat_reprFast(v_fnIdx_4924_);
v___x_4938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
v___x_4939_ = l_Lean_MessageData_ofFormat(v___x_4938_);
v___x_4940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4936_);
lean_ctor_set(v___x_4940_, 1, v___x_4939_);
v___x_4941_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_4942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4940_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = lean_array_to_list(v_positions_4923_);
v___x_4944_ = lean_box(0);
v___x_4945_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_4943_, v___x_4944_);
v___x_4946_ = l_Lean_MessageData_ofList(v___x_4945_);
v___x_4947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4942_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
v___x_4948_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4947_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
return v___x_4948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_4974_, lean_object* v_positions_4975_, lean_object* v_fnIdx_4976_, lean_object* v_brecOnConst_4977_, lean_object* v_packedFArgs_4978_, lean_object* v_funTypes_4979_, lean_object* v_ys_4980_, lean_object* v___value_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_4974_, v_positions_4975_, v_fnIdx_4976_, v_brecOnConst_4977_, v_packedFArgs_4978_, v_funTypes_4979_, v_ys_4980_, v___value_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
lean_dec_ref(v___value_4981_);
lean_dec_ref(v_funTypes_4979_);
lean_dec_ref(v_packedFArgs_4978_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_4988_, lean_object* v_fnIdx_4989_, lean_object* v_brecOnConst_4990_, lean_object* v_packedFArgs_4991_, lean_object* v_funTypes_4992_, lean_object* v_recArgInfo_4993_, lean_object* v_value_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_){
_start:
{
lean_object* v___f_5000_; uint8_t v___x_5001_; lean_object* v___x_5002_; 
v___f_5000_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5000_, 0, v_recArgInfo_4993_);
lean_closure_set(v___f_5000_, 1, v_positions_4988_);
lean_closure_set(v___f_5000_, 2, v_fnIdx_4989_);
lean_closure_set(v___f_5000_, 3, v_brecOnConst_4990_);
lean_closure_set(v___f_5000_, 4, v_packedFArgs_4991_);
lean_closure_set(v___f_5000_, 5, v_funTypes_4992_);
v___x_5001_ = 0;
v___x_5002_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4994_, v___f_5000_, v___x_5001_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5003_, lean_object* v_fnIdx_5004_, lean_object* v_brecOnConst_5005_, lean_object* v_packedFArgs_5006_, lean_object* v_funTypes_5007_, lean_object* v_recArgInfo_5008_, lean_object* v_value_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5003_, v_fnIdx_5004_, v_brecOnConst_5005_, v_packedFArgs_5006_, v_funTypes_5007_, v_recArgInfo_5008_, v_value_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
lean_dec(v_a_5013_);
lean_dec_ref(v_a_5012_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
return v_res_5015_;
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
