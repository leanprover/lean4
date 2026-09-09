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
extern lean_object* l_Lean_instInhabitedExpr;
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
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_124_; 
lean_dec_ref(v_e_102_);
v___x_124_ = l_Lean_Meta_saveState___redArg(v_a_106_, v_a_108_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__2));
v___x_127_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_103_);
v___x_128_ = l_Lean_Expr_proj___override(v___x_126_, v___x_127_, v_F_103_);
lean_inc_ref(v_k_104_);
v___x_129_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_117_, v___x_128_, v_k_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_dec(v_a_125_);
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
v___x_133_ = l_Lean_Meta_SavedState_restore___redArg(v_a_125_, v_a_106_, v_a_108_);
lean_dec(v_a_125_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec_ref_known(v___x_133_, 1);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = l_Lean_Expr_proj___override(v___x_126_, v___x_134_, v_F_103_);
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
lean_dec(v_a_125_);
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
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
v_a_147_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_124_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_124_);
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
lean_object* v___x_155_; 
lean_dec_ref(v_str_118_);
lean_dec_ref(v_e_102_);
v___x_155_ = l_Lean_Meta_saveState___redArg(v_a_106_, v_a_108_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
v___x_157_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__3));
v___x_158_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_103_);
v___x_159_ = l_Lean_Expr_proj___override(v___x_157_, v___x_158_, v_F_103_);
lean_inc_ref(v_k_104_);
v___x_160_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_117_, v___x_159_, v_k_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_dec(v_a_156_);
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
v___x_164_ = l_Lean_Meta_SavedState_restore___redArg(v_a_156_, v_a_106_, v_a_108_);
lean_dec(v_a_156_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref_known(v___x_164_, 1);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = l_Lean_Expr_proj___override(v___x_157_, v___x_165_, v_F_103_);
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
lean_dec(v_a_156_);
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
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_k_104_);
lean_dec_ref(v_F_103_);
v_a_178_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_155_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_155_);
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
lean_object* v___x_384_; double v___x_385_; uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_384_ = lean_box(0);
v___x_385_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_386_ = 0;
v___x_387_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_388_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_388_, 0, v_cls_353_);
lean_ctor_set(v___x_388_, 1, v___x_384_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
lean_ctor_set_float(v___x_388_, sizeof(void*)*3, v___x_385_);
lean_ctor_set_float(v___x_388_, sizeof(void*)*3 + 8, v___x_385_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*3 + 16, v___x_386_);
v___x_389_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_390_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v_a_362_);
lean_ctor_set(v___x_390_, 2, v___x_389_);
lean_inc(v_ref_360_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_ref_360_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_PersistentArray_push___redArg(v_traces_380_, v___x_391_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_392_);
v___x_394_ = v___x_382_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_392_);
lean_ctor_set_uint64(v_reuseFailAlloc_403_, sizeof(void*)*1, v_tid_379_);
v___x_394_ = v_reuseFailAlloc_403_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 4, v___x_394_);
v___x_396_ = v___x_377_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_env_368_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_nextMacroScope_369_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_ngen_370_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_auxDeclNGen_371_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_402_, 5, v_cache_372_);
lean_ctor_set(v_reuseFailAlloc_402_, 6, v_messages_373_);
lean_ctor_set(v_reuseFailAlloc_402_, 7, v_infoState_374_);
lean_ctor_set(v_reuseFailAlloc_402_, 8, v_snapshotTasks_375_);
v___x_396_ = v_reuseFailAlloc_402_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_st_ref_put(v___y_358_, v___x_396_);
v___x_398_ = lean_box(0);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_398_);
v___x_400_ = v___x_364_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v___f_421_, lean_object* v_a_422_, lean_object* v_C_423_, lean_object* v_cls_424_, lean_object* v_belowDict_425_, lean_object* v_F_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___x_505_; 
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
v___x_505_ = lean_apply_5(v___f_421_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, lean_box(0));
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; uint8_t v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
if (v___x_507_ == 0)
{
v___y_466_ = v___y_427_;
v___y_467_ = v___y_428_;
v___y_468_ = v___y_429_;
v___y_469_ = v___y_430_;
goto v___jp_465_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_508_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_425_);
v___x_509_ = l_Lean_indentExpr(v_belowDict_425_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
lean_inc(v_cls_424_);
v___x_511_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_424_, v___x_510_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_dec_ref_known(v___x_511_, 1);
v___y_466_ = v___y_427_;
v___y_467_ = v___y_428_;
v___y_468_ = v___y_429_;
v___y_469_ = v___y_430_;
goto v___jp_465_;
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_F_426_);
lean_dec_ref(v_belowDict_425_);
lean_dec(v_cls_424_);
lean_dec_ref(v_a_422_);
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
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_F_426_);
lean_dec_ref(v_belowDict_425_);
lean_dec(v_cls_424_);
lean_dec_ref(v_a_422_);
v_a_520_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_505_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_505_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
v___jp_432_:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_isExprDefEq(v___y_433_, v_a_422_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
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
lean_object* v_fn_470_; lean_object* v_arg_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
lean_dec(v_cls_424_);
v_fn_470_ = lean_ctor_get(v_belowDict_425_, 0);
lean_inc_ref(v_fn_470_);
v_arg_471_ = lean_ctor_get(v_belowDict_425_, 1);
lean_inc_ref(v_arg_471_);
lean_dec_ref_known(v_belowDict_425_, 2);
v___x_472_ = l_Lean_Expr_getAppFn(v_fn_470_);
lean_dec_ref(v_fn_470_);
v___x_473_ = lean_expr_eqv(v___x_472_, v_C_423_);
lean_dec_ref(v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v_arg_471_);
lean_dec_ref(v_F_426_);
lean_dec_ref(v_a_422_);
v___x_474_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_466_, v___y_467_, v___y_468_, v___y_469_);
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
v___y_433_ = v_arg_471_;
v___y_434_ = v___y_466_;
v___y_435_ = v___y_467_;
v___y_436_ = v___y_468_;
v___y_437_ = v___y_469_;
goto v___jp_432_;
}
}
else
{
lean_object* v_toCold_483_; lean_object* v_options_484_; uint8_t v_hasTrace_485_; 
lean_dec_ref(v_F_426_);
lean_dec_ref(v_a_422_);
v_toCold_483_ = lean_ctor_get(v___y_468_, 0);
v_options_484_ = lean_ctor_get(v_toCold_483_, 2);
v_hasTrace_485_ = lean_ctor_get_uint8(v_options_484_, sizeof(void*)*1);
if (v_hasTrace_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec_ref(v_belowDict_425_);
lean_dec(v_cls_424_);
v___x_486_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_486_;
}
else
{
lean_object* v_inheritedTraceOptions_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_inheritedTraceOptions_487_ = lean_ctor_get(v_toCold_483_, 11);
v___x_488_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_424_);
v___x_489_ = l_Lean_Name_append(v___x_488_, v_cls_424_);
v___x_490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_487_, v_options_484_, v___x_489_);
lean_dec(v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec_ref(v_belowDict_425_);
lean_dec(v_cls_424_);
v___x_491_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_492_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_493_ = l_Lean_indentExpr(v_belowDict_425_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_424_, v___x_494_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_496_; 
lean_dec_ref_known(v___x_495_, 1);
v___x_496_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_466_, v___y_467_, v___y_468_, v___y_469_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v___f_528_, lean_object* v_a_529_, lean_object* v_C_530_, lean_object* v_cls_531_, lean_object* v_belowDict_532_, lean_object* v_F_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v___f_528_, v_a_529_, v_C_530_, v_cls_531_, v_belowDict_532_, v_F_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec_ref(v_C_530_);
return v_res_539_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0(void){
_start:
{
lean_object* v___x_540_; lean_object* v_dummy_541_; 
v___x_540_ = lean_box(0);
v_dummy_541_ = l_Lean_Expr_sort___override(v___x_540_);
return v_dummy_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_542_, lean_object* v___f_543_, lean_object* v_C_544_, lean_object* v_cls_545_, lean_object* v_F_546_, lean_object* v_xs_547_, lean_object* v_belowDict_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
uint8_t v___x_554_; lean_object* v___x_555_; 
v___x_554_ = 1;
v___x_555_ = l_Lean_Meta_zetaReduce(v_arg_542_, v___x_554_, v___x_554_, v___x_554_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___f_557_; lean_object* v_dummy_558_; lean_object* v_nargs_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc_n(v_a_556_, 2);
lean_dec_ref_known(v___x_555_, 1);
v___f_557_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed), 11, 4);
lean_closure_set(v___f_557_, 0, v___f_543_);
lean_closure_set(v___f_557_, 1, v_a_556_);
lean_closure_set(v___f_557_, 2, v_C_544_);
lean_closure_set(v___f_557_, 3, v_cls_545_);
v_dummy_558_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_559_ = l_Lean_Expr_getAppNumArgs(v_a_556_);
lean_inc(v_nargs_559_);
v___x_560_ = lean_mk_array(v_nargs_559_, v_dummy_558_);
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = lean_nat_sub(v_nargs_559_, v___x_561_);
lean_dec(v_nargs_559_);
v___x_563_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_556_, v___x_560_, v___x_562_);
v___x_576_ = lean_array_get_size(v_xs_547_);
v___x_577_ = lean_array_get_size(v___x_563_);
v___x_578_ = lean_nat_dec_le(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v___x_563_);
lean_dec_ref(v___f_557_);
lean_dec_ref(v_F_546_);
v___x_579_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_549_, v___y_550_, v___y_551_, v___y_552_);
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
v___y_565_ = v___y_549_;
v___y_566_ = v___y_550_;
v___y_567_ = v___y_551_;
v___y_568_ = v___y_552_;
goto v___jp_564_;
}
v___jp_564_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_569_ = lean_array_get_size(v___x_563_);
v___x_570_ = lean_array_get_size(v_xs_547_);
v___x_571_ = lean_nat_sub(v___x_569_, v___x_570_);
v___x_572_ = l_Array_extract___redArg(v___x_563_, v___x_571_, v___x_569_);
lean_dec_ref(v___x_563_);
v___x_573_ = l_Lean_Expr_replaceFVars(v_belowDict_548_, v_xs_547_, v___x_572_);
v___x_574_ = l_Lean_mkAppN(v_F_546_, v___x_572_);
lean_dec_ref(v___x_572_);
v___x_575_ = l_Lean_Elab_Structural_searchPProd___redArg(v___x_573_, v___x_574_, v___f_557_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_575_;
}
}
else
{
lean_dec_ref(v_F_546_);
lean_dec(v_cls_545_);
lean_dec_ref(v_C_544_);
lean_dec_ref(v___f_543_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_588_, lean_object* v___f_589_, lean_object* v_C_590_, lean_object* v_cls_591_, lean_object* v_F_592_, lean_object* v_xs_593_, lean_object* v_belowDict_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_588_, v___f_589_, v_C_590_, v_cls_591_, v_F_592_, v_xs_593_, v_belowDict_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec_ref(v_belowDict_594_);
lean_dec_ref(v_xs_593_);
return v_res_600_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0));
v___x_603_ = l_Lean_stringToMessageData(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v___f_604_, lean_object* v_arg_605_, lean_object* v_C_606_, lean_object* v_cls_607_, lean_object* v_belowDict_608_, lean_object* v_F_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; 
lean_inc_ref(v___f_604_);
lean_inc(v___y_613_);
lean_inc_ref(v___y_612_);
lean_inc(v___y_611_);
lean_inc_ref(v___y_610_);
v___x_615_ = lean_apply_5(v___f_604_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, lean_box(0));
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___f_617_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; uint8_t v___x_625_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
lean_inc(v_cls_607_);
v___f_617_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_617_, 0, v_arg_605_);
lean_closure_set(v___f_617_, 1, v___f_604_);
lean_closure_set(v___f_617_, 2, v_C_606_);
lean_closure_set(v___f_617_, 3, v_cls_607_);
lean_closure_set(v___f_617_, 4, v_F_609_);
v___x_625_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
if (v___x_625_ == 0)
{
lean_dec(v_cls_607_);
v___y_619_ = v___y_610_;
v___y_620_ = v___y_611_;
v___y_621_ = v___y_612_;
v___y_622_ = v___y_613_;
goto v___jp_618_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_608_);
v___x_627_ = l_Lean_indentExpr(v_belowDict_608_);
v___x_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_607_, v___x_628_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_dec_ref_known(v___x_629_, 1);
v___y_619_ = v___y_610_;
v___y_620_ = v___y_611_;
v___y_621_ = v___y_612_;
v___y_622_ = v___y_613_;
goto v___jp_618_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v___f_617_);
lean_dec_ref(v_belowDict_608_);
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
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
}
v___jp_618_:
{
uint8_t v___x_623_; lean_object* v___x_624_; 
v___x_623_ = 0;
v___x_624_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_608_, v___f_617_, v___x_623_, v___x_623_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
return v___x_624_;
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v_F_609_);
lean_dec_ref(v_belowDict_608_);
lean_dec(v_cls_607_);
lean_dec_ref(v_C_606_);
lean_dec_ref(v_arg_605_);
lean_dec_ref(v___f_604_);
v_a_638_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_615_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_615_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v___f_646_, lean_object* v_arg_647_, lean_object* v_C_648_, lean_object* v_cls_649_, lean_object* v_belowDict_650_, lean_object* v_F_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v___f_646_, v_arg_647_, v_C_648_, v_cls_649_, v_belowDict_650_, v_F_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_657_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_669_ = l_Lean_stringToMessageData(v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_672_ = l_Lean_stringToMessageData(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_673_, lean_object* v_belowDict_674_, lean_object* v_arg_675_, lean_object* v_F_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_cls_682_; lean_object* v___f_683_; lean_object* v___x_684_; lean_object* v_a_685_; lean_object* v___f_686_; uint8_t v___x_687_; 
v_cls_682_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_683_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
v___x_684_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_682_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref(v___x_684_);
lean_inc_ref(v_arg_675_);
v___f_686_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_686_, 0, v___f_683_);
lean_closure_set(v___f_686_, 1, v_arg_675_);
lean_closure_set(v___f_686_, 2, v_C_673_);
lean_closure_set(v___f_686_, 3, v_cls_682_);
v___x_687_ = lean_unbox(v_a_685_);
lean_dec(v_a_685_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec_ref(v_arg_675_);
v___x_688_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_674_, v_F_676_, v___f_686_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_689_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_674_);
v___x_690_ = l_Lean_indentExpr(v_belowDict_674_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_indentExpr(v_arg_675_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_682_, v___x_695_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_697_; 
lean_dec_ref_known(v___x_696_, 1);
v___x_697_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_674_, v_F_676_, v___f_686_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_697_;
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v___f_686_);
lean_dec_ref(v_F_676_);
lean_dec_ref(v_belowDict_674_);
v_a_698_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_696_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_706_, lean_object* v_belowDict_707_, lean_object* v_arg_708_, lean_object* v_F_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_706_, v_belowDict_707_, v_arg_708_, v_F_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v___x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_toCold_722_; lean_object* v_options_723_; uint8_t v_hasTrace_724_; 
v_toCold_722_ = lean_ctor_get(v___y_719_, 0);
v_options_723_ = lean_ctor_get(v_toCold_722_, 2);
v_hasTrace_724_ = lean_ctor_get_uint8(v_options_723_, sizeof(void*)*1);
if (v_hasTrace_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v___x_716_);
v___x_725_ = lean_box(v_hasTrace_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
else
{
lean_object* v_inheritedTraceOptions_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_inheritedTraceOptions_727_ = lean_ctor_get(v_toCold_722_, 11);
v___x_728_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_729_ = l_Lean_Name_append(v___x_728_, v___x_716_);
v___x_730_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_727_, v_options_723_, v___x_729_);
lean_dec(v___x_729_);
v___x_731_ = lean_box(v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v___x_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_t_740_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_748_, lean_object* v_x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_748_, v_x_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec_ref(v_x_749_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v_t_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__1));
v___x_766_ = l_Lean_Core_mkFreshUserName(v___x_765_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_776_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_776_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___f_771_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_771_, 0, v_t_759_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_a_767_);
lean_ctor_set(v___x_772_, 1, v___f_771_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v_t_759_);
v_a_777_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_766_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_766_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v_t_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v_t_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_792_, lean_object* v_a_793_, lean_object* v_x_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_array_set(v___y_795_, v_a_793_, v___x_792_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_804_, lean_object* v_a_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_804_, v_a_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v_a_805_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_814_, lean_object* v_a_815_, lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_snd_823_; lean_object* v_fst_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_875_; 
v_snd_823_ = lean_ctor_get(v___y_817_, 1);
v_fst_824_ = lean_ctor_get(v___y_817_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___y_817_);
if (v_isSharedCheck_875_ == 0)
{
v___x_826_ = v___y_817_;
v_isShared_827_ = v_isSharedCheck_875_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_snd_823_);
lean_inc(v_fst_824_);
lean_dec(v___y_817_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_875_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_array_828_; lean_object* v_start_829_; lean_object* v_stop_830_; uint8_t v___x_831_; 
v_array_828_ = lean_ctor_get(v_snd_823_, 0);
v_start_829_ = lean_ctor_get(v_snd_823_, 1);
v_stop_830_ = lean_ctor_get(v_snd_823_, 2);
v___x_831_ = lean_nat_dec_lt(v_start_829_, v_stop_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_833_; 
lean_dec_ref(v_a_815_);
lean_dec_ref(v___x_814_);
if (v_isShared_827_ == 0)
{
v___x_833_ = v___x_826_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_fst_824_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_snd_823_);
v___x_833_ = v_reuseFailAlloc_836_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
else
{
lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_871_; 
lean_inc(v_stop_830_);
lean_inc(v_start_829_);
lean_inc_ref(v_array_828_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_snd_823_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; 
v_unused_872_ = lean_ctor_get(v_snd_823_, 2);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_snd_823_, 1);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_snd_823_, 0);
lean_dec(v_unused_874_);
v___x_838_ = v_snd_823_;
v_isShared_839_ = v_isSharedCheck_871_;
goto v_resetjp_837_;
}
else
{
lean_dec(v_snd_823_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_871_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___f_841_; size_t v_sz_842_; size_t v___x_843_; lean_object* v___x_7136__overap_844_; lean_object* v___x_845_; 
v___x_840_ = lean_array_fget_borrowed(v_array_828_, v_start_829_);
lean_inc(v___x_840_);
v___f_841_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_841_, 0, v___x_840_);
v_sz_842_ = lean_array_size(v_a_815_);
v___x_843_ = ((size_t)0ULL);
v___x_7136__overap_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_814_, v_a_815_, v___f_841_, v_sz_842_, v___x_843_, v_fst_824_);
lean_inc(v___y_821_);
lean_inc_ref(v___y_820_);
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
v___x_845_ = lean_apply_5(v___x_7136__overap_844_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, lean_box(0));
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_862_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_862_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_862_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_862_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_add(v_start_829_, v___x_850_);
lean_dec(v_start_829_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_851_);
v___x_853_ = v___x_838_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_array_828_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_stop_830_);
v___x_853_ = v_reuseFailAlloc_861_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_855_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v___x_853_);
lean_ctor_set(v___x_826_, 0, v_a_846_);
v___x_855_ = v___x_826_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_846_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_860_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_856_);
v___x_858_ = v___x_848_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_del_object(v___x_838_);
lean_dec(v_stop_830_);
lean_dec(v_start_829_);
lean_dec_ref(v_array_828_);
lean_del_object(v___x_826_);
v_a_863_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_845_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_845_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_876_, lean_object* v_a_877_, lean_object* v_x_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_876_, v_a_877_, v_x_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_885_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6));
v___x_896_ = l_Lean_stringToMessageData(v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_positions_899_, lean_object* v_a_900_, lean_object* v___f_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v_k_904_, lean_object* v___x_905_, lean_object* v___x_906_, lean_object* v_toMonadRef_907_, lean_object* v___x_908_, lean_object* v_Cs_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_7163__overap_916_; lean_object* v___x_917_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_909_);
lean_inc_ref(v___x_897_);
v___x_7163__overap_916_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_897_, v___x_898_, v___x_915_, v_positions_899_, v_a_900_, v_Cs_909_);
lean_inc(v___y_913_);
lean_inc_ref(v___y_912_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
v___x_917_ = lean_apply_5(v___x_7163__overap_916_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, lean_box(0));
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
lean_inc(v___y_913_);
lean_inc_ref(v___y_912_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
v___x_919_ = lean_apply_5(v___f_901_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, lean_box(0));
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; uint8_t v___x_962_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = l_Lean_mkAppN(v___x_902_, v_a_918_);
lean_dec(v_a_918_);
v___x_922_ = l_Subarray_copy___redArg(v___x_903_);
v___x_923_ = l_Lean_mkAppN(v___x_921_, v___x_922_);
lean_dec_ref(v___x_922_);
v___x_962_ = lean_unbox(v_a_920_);
lean_dec(v_a_920_);
if (v___x_962_ == 0)
{
v___y_925_ = v___y_910_;
v___y_926_ = v___y_911_;
v___y_927_ = v___y_912_;
v___y_928_ = v___y_913_;
goto v___jp_924_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_7213__overap_974_; lean_object* v___x_975_; 
v___x_963_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_Cs_909_);
v___x_964_ = lean_array_to_list(v_Cs_909_);
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_966_ = lean_box(0);
v___x_967_ = l_List_mapTR_loop___redArg(v___x_965_, v___x_964_, v___x_966_);
v___x_968_ = l_Lean_MessageData_ofList(v___x_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_963_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
lean_inc_ref(v___x_923_);
v___x_972_ = l_Lean_indentExpr(v___x_923_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
lean_inc(v___x_905_);
lean_inc_ref(v___x_908_);
lean_inc_ref(v_toMonadRef_907_);
lean_inc_ref(v___x_906_);
lean_inc_ref(v___x_897_);
v___x_7213__overap_974_ = l_Lean_addTrace___redArg(v___x_897_, v___x_906_, v_toMonadRef_907_, v___x_908_, v___x_905_, v___x_973_);
lean_inc(v___y_913_);
lean_inc_ref(v___y_912_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
v___x_975_ = lean_apply_5(v___x_7213__overap_974_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, lean_box(0));
if (lean_obj_tag(v___x_975_) == 0)
{
lean_dec_ref_known(v___x_975_, 1);
v___y_925_ = v___y_910_;
v___y_926_ = v___y_911_;
v___y_927_ = v___y_912_;
v___y_928_ = v___y_913_;
goto v___jp_924_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v___x_923_);
lean_dec_ref(v_Cs_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_toMonadRef_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___x_905_);
lean_dec_ref(v_k_904_);
lean_dec_ref(v___x_897_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
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
}
v___jp_924_:
{
lean_object* v___x_929_; 
lean_inc_ref(v___x_923_);
v___x_929_ = l_Lean_Meta_isTypeCorrect(v___x_923_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; uint8_t v___x_931_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = lean_unbox(v_a_930_);
lean_dec(v_a_930_);
if (v___x_931_ == 0)
{
lean_object* v_toCold_932_; lean_object* v_options_933_; uint8_t v_hasTrace_934_; 
v_toCold_932_ = lean_ctor_get(v___y_927_, 0);
v_options_933_ = lean_ctor_get(v_toCold_932_, 2);
v_hasTrace_934_ = lean_ctor_get_uint8(v_options_933_, sizeof(void*)*1);
if (v_hasTrace_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec_ref(v___x_908_);
lean_dec_ref(v_toMonadRef_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___x_905_);
lean_dec_ref(v___x_897_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
v___x_935_ = lean_apply_7(v_k_904_, v_Cs_909_, v___x_923_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
return v___x_935_;
}
else
{
lean_object* v_inheritedTraceOptions_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_inheritedTraceOptions_936_ = lean_ctor_get(v_toCold_932_, 11);
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_905_);
v___x_938_ = l_Lean_Name_append(v___x_937_, v___x_905_);
v___x_939_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_936_, v_options_933_, v___x_938_);
lean_dec(v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_dec_ref(v___x_908_);
lean_dec_ref(v_toMonadRef_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___x_905_);
lean_dec_ref(v___x_897_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
v___x_940_ = lean_apply_7(v_k_904_, v_Cs_909_, v___x_923_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
return v___x_940_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_7189__overap_942_; lean_object* v___x_943_; 
v___x_941_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
v___x_7189__overap_942_ = l_Lean_addTrace___redArg(v___x_897_, v___x_906_, v_toMonadRef_907_, v___x_908_, v___x_905_, v___x_941_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
v___x_943_ = lean_apply_5(v___x_7189__overap_942_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_944_; 
lean_dec_ref_known(v___x_943_, 1);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
v___x_944_ = lean_apply_7(v_k_904_, v_Cs_909_, v___x_923_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
return v___x_944_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v___x_923_);
lean_dec_ref(v_Cs_909_);
lean_dec_ref(v_k_904_);
v_a_945_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_943_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
else
{
lean_object* v___x_953_; 
lean_dec_ref(v___x_908_);
lean_dec_ref(v_toMonadRef_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___x_905_);
lean_dec_ref(v___x_897_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
v___x_953_ = lean_apply_7(v_k_904_, v_Cs_909_, v___x_923_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
return v___x_953_;
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___x_923_);
lean_dec_ref(v_Cs_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_toMonadRef_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___x_905_);
lean_dec_ref(v_k_904_);
lean_dec_ref(v___x_897_);
v_a_954_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_929_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_929_);
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
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_a_918_);
lean_dec_ref(v_Cs_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_toMonadRef_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___x_905_);
lean_dec_ref(v_k_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_897_);
v_a_984_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_919_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_919_);
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
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v_Cs_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_toMonadRef_907_);
lean_dec_ref(v___x_906_);
lean_dec(v___x_905_);
lean_dec_ref(v_k_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___f_901_);
lean_dec_ref(v___x_897_);
v_a_992_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_917_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_917_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_1000_ = _args[0];
lean_object* v___x_1001_ = _args[1];
lean_object* v_positions_1002_ = _args[2];
lean_object* v_a_1003_ = _args[3];
lean_object* v___f_1004_ = _args[4];
lean_object* v___x_1005_ = _args[5];
lean_object* v___x_1006_ = _args[6];
lean_object* v_k_1007_ = _args[7];
lean_object* v___x_1008_ = _args[8];
lean_object* v___x_1009_ = _args[9];
lean_object* v_toMonadRef_1010_ = _args[10];
lean_object* v___x_1011_ = _args[11];
lean_object* v_Cs_1012_ = _args[12];
lean_object* v___y_1013_ = _args[13];
lean_object* v___y_1014_ = _args[14];
lean_object* v___y_1015_ = _args[15];
lean_object* v___y_1016_ = _args[16];
lean_object* v___y_1017_ = _args[17];
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_1000_, v___x_1001_, v_positions_1002_, v_a_1003_, v___f_1004_, v___x_1005_, v___x_1006_, v_k_1007_, v___x_1008_, v___x_1009_, v_toMonadRef_1010_, v___x_1011_, v_Cs_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1018_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_unsigned_to_nat(37u);
v___x_1020_ = l_Lean_Level_ofNat(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1022_ = l_Lean_Expr_sort___override(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1029_, lean_object* v___x_1030_, lean_object* v___f_1031_, lean_object* v___f_1032_, lean_object* v___x_1033_, lean_object* v_numTypeFormers_1034_, lean_object* v___f_1035_, lean_object* v___x_1036_, lean_object* v_k_1037_, lean_object* v___x_1038_, lean_object* v___x_1039_, lean_object* v_toMonadRef_1040_, lean_object* v___x_1041_, lean_object* v_numIndParams_1042_, lean_object* v_a_1043_, lean_object* v_f_1044_, lean_object* v_args_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1177_ = lean_nat_add(v_numIndParams_1042_, v_numTypeFormers_1034_);
v___x_1178_ = lean_array_get_size(v_args_1045_);
v___x_1179_ = lean_nat_dec_lt(v___x_1177_, v___x_1178_);
lean_dec(v___x_1177_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_dec_ref(v_args_1045_);
lean_dec_ref(v_f_1044_);
lean_dec(v_numIndParams_1042_);
lean_dec_ref(v_k_1037_);
lean_dec_ref(v___x_1036_);
lean_dec(v_numTypeFormers_1034_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_positions_1029_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
v___x_1180_ = lean_apply_5(v___f_1035_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, lean_box(0));
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; uint8_t v___x_1182_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = lean_unbox(v_a_1181_);
lean_dec(v_a_1181_);
if (v___x_1182_ == 0)
{
lean_dec_ref(v_a_1043_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_toMonadRef_1040_);
lean_dec_ref(v___x_1039_);
lean_dec(v___x_1038_);
lean_dec_ref(v___x_1030_);
v___y_1164_ = v___y_1046_;
v___y_1165_ = v___y_1047_;
v___y_1166_ = v___y_1048_;
v___y_1167_ = v___y_1049_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_7345__overap_1186_; lean_object* v___x_1187_; 
v___x_1183_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1184_ = l_Lean_indentExpr(v_a_1043_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_7345__overap_1186_ = l_Lean_addTrace___redArg(v___x_1030_, v___x_1039_, v_toMonadRef_1040_, v___x_1041_, v___x_1038_, v___x_1185_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
v___x_1187_ = lean_apply_5(v___x_7345__overap_1186_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, lean_box(0));
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_dec_ref_known(v___x_1187_, 1);
v___y_1164_ = v___y_1046_;
v___y_1165_ = v___y_1047_;
v___y_1166_ = v___y_1048_;
v___y_1167_ = v___y_1049_;
goto v___jp_1163_;
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_a_1043_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_toMonadRef_1040_);
lean_dec_ref(v___x_1039_);
lean_dec(v___x_1038_);
lean_dec_ref(v___x_1030_);
v_a_1196_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1180_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1180_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_dec_ref(v_a_1043_);
v___y_1152_ = v___y_1046_;
v___y_1153_ = v___y_1047_;
v___y_1154_ = v___y_1048_;
v___y_1155_ = v___y_1049_;
goto v___jp_1151_;
}
v___jp_1051_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; size_t v_sz_1065_; size_t v___x_1066_; lean_object* v___x_7258__overap_1067_; lean_object* v___x_1068_; 
v___x_1060_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1061_ = lean_mk_array(v___y_1053_, v___x_1060_);
v___x_1062_ = lean_array_get_size(v___y_1052_);
v___x_1063_ = l_Array_toSubarray___redArg(v___y_1052_, v___y_1054_, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1061_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v_sz_1065_ = lean_array_size(v_positions_1029_);
v___x_1066_ = ((size_t)0ULL);
lean_inc_ref(v___x_1030_);
v___x_7258__overap_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1030_, v_positions_1029_, v___f_1031_, v_sz_1065_, v___x_1066_, v___x_1064_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
v___x_1068_ = lean_apply_5(v___x_7258__overap_1067_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, lean_box(0));
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v_fst_1070_; size_t v_sz_1071_; lean_object* v___x_7261__overap_1072_; lean_object* v___x_1073_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v_fst_1070_ = lean_ctor_get(v_a_1069_, 0);
lean_inc(v_fst_1070_);
lean_dec(v_a_1069_);
v_sz_1071_ = lean_array_size(v_fst_1070_);
lean_inc_ref(v___x_1030_);
v___x_7261__overap_1072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1030_, v___f_1032_, v_sz_1071_, v___x_1066_, v_fst_1070_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
v___x_1073_ = lean_apply_5(v___x_7261__overap_1072_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, lean_box(0));
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; uint8_t v___x_1075_; lean_object* v___x_7265__overap_1076_; lean_object* v___x_1077_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1075_ = 0;
v___x_7265__overap_1076_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1033_, v___x_1030_, v_a_1074_, v___y_1055_, v___x_1075_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
v___x_1077_ = lean_apply_5(v___x_7265__overap_1076_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, lean_box(0));
return v___x_1077_;
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v___y_1055_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___x_1030_);
v_a_1078_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1073_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1073_);
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
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v___y_1055_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___x_1030_);
v_a_1086_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1068_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1068_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
v___jp_1094_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = l_Subarray_copy___redArg(v___y_1097_);
v___x_1103_ = l_Lean_mkAppN(v_f_1044_, v___x_1102_);
lean_dec_ref(v___x_1102_);
lean_inc_ref(v___x_1103_);
v___x_1104_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1034_, v___x_1103_, v___y_1099_, v___y_1095_, v___y_1096_, v___y_1098_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
lean_inc_ref(v___f_1035_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1099_);
v___x_1106_ = lean_apply_5(v___f_1035_, v___y_1099_, v___y_1095_, v___y_1096_, v___y_1098_, lean_box(0));
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v_lower_1108_; lean_object* v_upper_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1134_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v_lower_1108_ = lean_ctor_get(v___y_1101_, 0);
v_upper_1109_ = lean_ctor_get(v___y_1101_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___y_1101_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1111_ = v___y_1101_;
v_isShared_1112_ = v_isSharedCheck_1134_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_upper_1109_);
lean_inc(v_lower_1108_);
lean_dec(v___y_1101_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1134_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1113_ = l_Array_toSubarray___redArg(v_args_1045_, v_lower_1108_, v_upper_1109_);
lean_inc_ref(v___x_1041_);
lean_inc_ref(v_toMonadRef_1040_);
lean_inc_ref(v___x_1039_);
lean_inc(v___x_1038_);
lean_inc(v_a_1105_);
lean_inc_ref(v_positions_1029_);
lean_inc_ref(v___x_1030_);
v___f_1114_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1114_, 0, v___x_1030_);
lean_closure_set(v___f_1114_, 1, v___x_1036_);
lean_closure_set(v___f_1114_, 2, v_positions_1029_);
lean_closure_set(v___f_1114_, 3, v_a_1105_);
lean_closure_set(v___f_1114_, 4, v___f_1035_);
lean_closure_set(v___f_1114_, 5, v___x_1103_);
lean_closure_set(v___f_1114_, 6, v___x_1113_);
lean_closure_set(v___f_1114_, 7, v_k_1037_);
lean_closure_set(v___f_1114_, 8, v___x_1038_);
lean_closure_set(v___f_1114_, 9, v___x_1039_);
lean_closure_set(v___f_1114_, 10, v_toMonadRef_1040_);
lean_closure_set(v___f_1114_, 11, v___x_1041_);
v___x_1115_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1029_);
v___x_1116_ = lean_unbox(v_a_1107_);
lean_dec(v_a_1107_);
if (v___x_1116_ == 0)
{
lean_del_object(v___x_1111_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_toMonadRef_1040_);
lean_dec_ref(v___x_1039_);
lean_dec(v___x_1038_);
v___y_1052_ = v_a_1105_;
v___y_1053_ = v___x_1115_;
v___y_1054_ = v___y_1100_;
v___y_1055_ = v___f_1114_;
v___y_1056_ = v___y_1099_;
v___y_1057_ = v___y_1095_;
v___y_1058_ = v___y_1096_;
v___y_1059_ = v___y_1098_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1117_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1115_);
v___x_1118_ = l_Nat_reprFast(v___x_1115_);
v___x_1119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 7);
lean_ctor_set(v___x_1111_, 1, v___x_1120_);
lean_ctor_set(v___x_1111_, 0, v___x_1117_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_7298__overap_1123_; lean_object* v___x_1124_; 
lean_inc_ref(v___x_1030_);
v___x_7298__overap_1123_ = l_Lean_addTrace___redArg(v___x_1030_, v___x_1039_, v_toMonadRef_1040_, v___x_1041_, v___x_1038_, v___x_1122_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1099_);
v___x_1124_ = lean_apply_5(v___x_7298__overap_1123_, v___y_1099_, v___y_1095_, v___y_1096_, v___y_1098_, lean_box(0));
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_dec_ref_known(v___x_1124_, 1);
v___y_1052_ = v_a_1105_;
v___y_1053_ = v___x_1115_;
v___y_1054_ = v___y_1100_;
v___y_1055_ = v___f_1114_;
v___y_1056_ = v___y_1099_;
v___y_1057_ = v___y_1095_;
v___y_1058_ = v___y_1096_;
v___y_1059_ = v___y_1098_;
goto v___jp_1051_;
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v___x_1115_);
lean_dec_ref(v___f_1114_);
lean_dec(v_a_1105_);
lean_dec(v___y_1100_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v_positions_1029_);
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_a_1105_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v_args_1045_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_toMonadRef_1040_);
lean_dec_ref(v___x_1039_);
lean_dec(v___x_1038_);
lean_dec_ref(v_k_1037_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v___f_1035_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v_positions_1029_);
v_a_1135_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1106_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1106_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v_args_1045_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_toMonadRef_1040_);
lean_dec_ref(v___x_1039_);
lean_dec(v___x_1038_);
lean_dec_ref(v_k_1037_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v___f_1035_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v_positions_1029_);
v_a_1143_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1104_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1104_);
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
v___jp_1151_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1042_);
lean_inc_ref(v_args_1045_);
v___x_1157_ = l_Array_toSubarray___redArg(v_args_1045_, v___x_1156_, v_numIndParams_1042_);
v___x_1158_ = lean_nat_add(v_numIndParams_1042_, v_numTypeFormers_1034_);
lean_dec(v_numIndParams_1042_);
v___x_1159_ = lean_array_get_size(v_args_1045_);
v___x_1160_ = lean_nat_dec_le(v___x_1158_, v___x_1156_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1158_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
v___y_1095_ = v___y_1153_;
v___y_1096_ = v___y_1154_;
v___y_1097_ = v___x_1157_;
v___y_1098_ = v___y_1155_;
v___y_1099_ = v___y_1152_;
v___y_1100_ = v___x_1156_;
v___y_1101_ = v___x_1161_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1162_; 
lean_dec(v___x_1158_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1156_);
lean_ctor_set(v___x_1162_, 1, v___x_1159_);
v___y_1095_ = v___y_1153_;
v___y_1096_ = v___y_1154_;
v___y_1097_ = v___x_1157_;
v___y_1098_ = v___y_1155_;
v___y_1099_ = v___y_1152_;
v___y_1100_ = v___x_1156_;
v___y_1101_ = v___x_1162_;
goto v___jp_1094_;
}
}
v___jp_1163_:
{
lean_object* v___x_1168_; lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v___x_1168_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1204_ = _args[0];
lean_object* v___x_1205_ = _args[1];
lean_object* v___f_1206_ = _args[2];
lean_object* v___f_1207_ = _args[3];
lean_object* v___x_1208_ = _args[4];
lean_object* v_numTypeFormers_1209_ = _args[5];
lean_object* v___f_1210_ = _args[6];
lean_object* v___x_1211_ = _args[7];
lean_object* v_k_1212_ = _args[8];
lean_object* v___x_1213_ = _args[9];
lean_object* v___x_1214_ = _args[10];
lean_object* v_toMonadRef_1215_ = _args[11];
lean_object* v___x_1216_ = _args[12];
lean_object* v_numIndParams_1217_ = _args[13];
lean_object* v_a_1218_ = _args[14];
lean_object* v_f_1219_ = _args[15];
lean_object* v_args_1220_ = _args[16];
lean_object* v___y_1221_ = _args[17];
lean_object* v___y_1222_ = _args[18];
lean_object* v___y_1223_ = _args[19];
lean_object* v___y_1224_ = _args[20];
lean_object* v___y_1225_ = _args[21];
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1204_, v___x_1205_, v___f_1206_, v___f_1207_, v___x_1208_, v_numTypeFormers_1209_, v___f_1210_, v___x_1211_, v_k_1212_, v___x_1213_, v___x_1214_, v_toMonadRef_1215_, v___x_1216_, v_numIndParams_1217_, v_a_1218_, v_f_1219_, v_args_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1226_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_instMonadEIO(lean_box(0));
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1229_ = l_StateRefT_x27_instMonad___redArg(v___x_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1238_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1237_, v___x_1236_);
return v___x_1238_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1240_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1241_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1240_, v___x_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1244_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1245_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1246_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
v___x_1247_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1246_, v___x_1245_, v___x_1244_);
return v___x_1247_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; 
v___x_1248_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1250_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1251_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1250_, v___f_1249_, v___x_1248_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16));
v___x_1257_ = l_Lean_stringToMessageData(v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1258_, lean_object* v_numIndParams_1259_, lean_object* v_positions_1260_, lean_object* v_k_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v___x_1267_; lean_object* v_toApplicative_1268_; lean_object* v_toFunctor_1269_; lean_object* v_toSeq_1270_; lean_object* v_toSeqLeft_1271_; lean_object* v_toSeqRight_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___f_1275_; lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___f_1278_; lean_object* v___f_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_toApplicative_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1406_; 
v___x_1267_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1268_ = lean_ctor_get(v___x_1267_, 0);
v_toFunctor_1269_ = lean_ctor_get(v_toApplicative_1268_, 0);
v_toSeq_1270_ = lean_ctor_get(v_toApplicative_1268_, 2);
v_toSeqLeft_1271_ = lean_ctor_get(v_toApplicative_1268_, 3);
v_toSeqRight_1272_ = lean_ctor_get(v_toApplicative_1268_, 4);
v___f_1273_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1274_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1269_, 2);
v___f_1275_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1275_, 0, v_toFunctor_1269_);
v___f_1276_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1276_, 0, v_toFunctor_1269_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___f_1275_);
lean_ctor_set(v___x_1277_, 1, v___f_1276_);
lean_inc(v_toSeqRight_1272_);
v___f_1278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1278_, 0, v_toSeqRight_1272_);
lean_inc(v_toSeqLeft_1271_);
v___f_1279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1279_, 0, v_toSeqLeft_1271_);
lean_inc(v_toSeq_1270_);
v___f_1280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1280_, 0, v_toSeq_1270_);
v___x_1281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1277_);
lean_ctor_set(v___x_1281_, 1, v___f_1273_);
lean_ctor_set(v___x_1281_, 2, v___f_1280_);
lean_ctor_set(v___x_1281_, 3, v___f_1279_);
lean_ctor_set(v___x_1281_, 4, v___f_1278_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___f_1274_);
v___x_1283_ = l_StateRefT_x27_instMonad___redArg(v___x_1282_);
v_toApplicative_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v___x_1283_, 1);
lean_dec(v_unused_1407_);
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1406_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_toApplicative_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1406_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_toFunctor_1288_; lean_object* v_toSeq_1289_; lean_object* v_toSeqLeft_1290_; lean_object* v_toSeqRight_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1404_; 
v_toFunctor_1288_ = lean_ctor_get(v_toApplicative_1284_, 0);
v_toSeq_1289_ = lean_ctor_get(v_toApplicative_1284_, 2);
v_toSeqLeft_1290_ = lean_ctor_get(v_toApplicative_1284_, 3);
v_toSeqRight_1291_ = lean_ctor_get(v_toApplicative_1284_, 4);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_toApplicative_1284_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; 
v_unused_1405_ = lean_ctor_get(v_toApplicative_1284_, 1);
lean_dec(v_unused_1405_);
v___x_1293_ = v_toApplicative_1284_;
v_isShared_1294_ = v_isSharedCheck_1404_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_toSeqRight_1291_);
lean_inc(v_toSeqLeft_1290_);
lean_inc(v_toSeq_1289_);
lean_inc(v_toFunctor_1288_);
lean_dec(v_toApplicative_1284_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1404_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___f_1297_; lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v___f_1300_; lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___x_1304_; 
v___f_1295_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1288_);
v___f_1297_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1297_, 0, v_toFunctor_1288_);
v___f_1298_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1298_, 0, v_toFunctor_1288_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___f_1297_);
lean_ctor_set(v___x_1299_, 1, v___f_1298_);
v___f_1300_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1300_, 0, v_toSeqRight_1291_);
v___f_1301_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1301_, 0, v_toSeqLeft_1290_);
v___f_1302_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1302_, 0, v_toSeq_1289_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___f_1300_);
lean_ctor_set(v___x_1293_, 3, v___f_1301_);
lean_ctor_set(v___x_1293_, 2, v___f_1302_);
lean_ctor_set(v___x_1293_, 1, v___f_1295_);
lean_ctor_set(v___x_1293_, 0, v___x_1299_);
v___x_1304_ = v___x_1293_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___f_1295_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v___f_1302_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v___f_1301_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v___f_1300_);
v___x_1304_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___f_1296_);
lean_ctor_set(v___x_1286_, 0, v___x_1304_);
v___x_1306_ = v___x_1286_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___f_1296_);
v___x_1306_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v_toApplicative_1308_; lean_object* v_toFunctor_1309_; lean_object* v_toSeq_1310_; lean_object* v_toSeqLeft_1311_; lean_object* v_toSeqRight_1312_; lean_object* v___f_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_toMonadRef_1325_; lean_object* v___x_1326_; 
v___x_1307_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1308_ = lean_ctor_get(v___x_1267_, 0);
v_toFunctor_1309_ = lean_ctor_get(v_toApplicative_1308_, 0);
v_toSeq_1310_ = lean_ctor_get(v_toApplicative_1308_, 2);
v_toSeqLeft_1311_ = lean_ctor_get(v_toApplicative_1308_, 3);
v_toSeqRight_1312_ = lean_ctor_get(v_toApplicative_1308_, 4);
lean_inc_ref_n(v_toFunctor_1309_, 2);
v___f_1313_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1313_, 0, v_toFunctor_1309_);
v___f_1314_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1314_, 0, v_toFunctor_1309_);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___f_1313_);
lean_ctor_set(v___x_1315_, 1, v___f_1314_);
lean_inc(v_toSeqRight_1312_);
v___f_1316_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1316_, 0, v_toSeqRight_1312_);
lean_inc(v_toSeqLeft_1311_);
v___f_1317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1317_, 0, v_toSeqLeft_1311_);
lean_inc(v_toSeq_1310_);
v___f_1318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1318_, 0, v_toSeq_1310_);
v___x_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1315_);
lean_ctor_set(v___x_1319_, 1, v___f_1273_);
lean_ctor_set(v___x_1319_, 2, v___f_1318_);
lean_ctor_set(v___x_1319_, 3, v___f_1317_);
lean_ctor_set(v___x_1319_, 4, v___f_1316_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___f_1274_);
v___x_1321_ = l_StateRefT_x27_instMonad___redArg(v___x_1320_);
v___x_1322_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1322_, 0, lean_box(0));
lean_closure_set(v___x_1322_, 1, lean_box(0));
lean_closure_set(v___x_1322_, 2, v___x_1321_);
v___x_1323_ = l_instMonadControlTOfPure___redArg(v___x_1322_);
v___x_1324_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1265_);
lean_inc_ref(v_a_1264_);
lean_inc(v_a_1263_);
lean_inc_ref(v_a_1262_);
lean_inc_ref(v_below_1258_);
v___x_1326_ = lean_infer_type(v_below_1258_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; lean_object* v___f_1329_; lean_object* v___x_1330_; lean_object* v_a_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_numTypeFormers_1336_; lean_object* v___f_1337_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___x_1380_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc_n(v_a_1327_, 2);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1329_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
v___x_1330_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1328_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref(v___x_1330_);
v___f_1332_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15));
lean_inc_ref_n(v___x_1306_, 2);
v___f_1333_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed), 9, 1);
lean_closure_set(v___f_1333_, 0, v___x_1306_);
v___x_1334_ = l_Lean_instInhabitedExpr;
v___x_1335_ = l_Lean_Meta_instAddMessageContextMetaM;
v_numTypeFormers_1336_ = lean_array_get_size(v_positions_1260_);
lean_inc_ref(v_toMonadRef_1325_);
v___f_1337_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1337_, 0, v_positions_1260_);
lean_closure_set(v___f_1337_, 1, v___x_1306_);
lean_closure_set(v___f_1337_, 2, v___f_1333_);
lean_closure_set(v___f_1337_, 3, v___f_1332_);
lean_closure_set(v___f_1337_, 4, v___x_1323_);
lean_closure_set(v___f_1337_, 5, v_numTypeFormers_1336_);
lean_closure_set(v___f_1337_, 6, v___f_1329_);
lean_closure_set(v___f_1337_, 7, v___x_1334_);
lean_closure_set(v___f_1337_, 8, v_k_1261_);
lean_closure_set(v___f_1337_, 9, v___x_1328_);
lean_closure_set(v___f_1337_, 10, v___x_1307_);
lean_closure_set(v___f_1337_, 11, v_toMonadRef_1325_);
lean_closure_set(v___f_1337_, 12, v___x_1335_);
lean_closure_set(v___f_1337_, 13, v_numIndParams_1259_);
lean_closure_set(v___f_1337_, 14, v_a_1327_);
v___x_1380_ = lean_unbox(v_a_1331_);
lean_dec(v_a_1331_);
if (v___x_1380_ == 0)
{
v___y_1351_ = v_a_1262_;
v___y_1352_ = v_a_1263_;
v___y_1353_ = v_a_1264_;
v___y_1354_ = v_a_1265_;
goto v___jp_1350_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_6878__overap_1384_; lean_object* v___x_1385_; 
v___x_1381_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17);
lean_inc(v_a_1327_);
v___x_1382_ = l_Lean_MessageData_ofExpr(v_a_1327_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
lean_inc_ref(v_toMonadRef_1325_);
lean_inc_ref(v___x_1306_);
v___x_6878__overap_1384_ = l_Lean_addTrace___redArg(v___x_1306_, v___x_1307_, v_toMonadRef_1325_, v___x_1335_, v___x_1328_, v___x_1383_);
lean_inc(v_a_1265_);
lean_inc_ref(v_a_1264_);
lean_inc(v_a_1263_);
lean_inc_ref(v_a_1262_);
v___x_1385_ = lean_apply_5(v___x_6878__overap_1384_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, lean_box(0));
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_dec_ref_known(v___x_1385_, 1);
v___y_1351_ = v_a_1262_;
v___y_1352_ = v_a_1263_;
v___y_1353_ = v_a_1264_;
v___y_1354_ = v_a_1265_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v___f_1337_);
lean_dec(v_a_1327_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v_below_1258_);
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
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
v___jp_1338_:
{
lean_object* v_dummy_1343_; lean_object* v_nargs_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_6849__overap_1348_; lean_object* v___x_1349_; 
v_dummy_1343_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1344_ = l_Lean_Expr_getAppNumArgs(v_a_1327_);
lean_inc(v_nargs_1344_);
v___x_1345_ = lean_mk_array(v_nargs_1344_, v_dummy_1343_);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_sub(v_nargs_1344_, v___x_1346_);
lean_dec(v_nargs_1344_);
v___x_6849__overap_1348_ = l_Lean_Expr_withAppAux___redArg(v___f_1337_, v_a_1327_, v___x_1345_, v___x_1347_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
v___x_1349_ = lean_apply_5(v___x_6849__overap_1348_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, lean_box(0));
return v___x_1349_;
}
v___jp_1350_:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Meta_isTypeCorrect(v_below_1258_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; uint8_t v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = lean_unbox(v_a_1356_);
lean_dec(v_a_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v_a_1359_; uint8_t v___x_1360_; 
v___x_1358_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1328_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref(v___x_1358_);
v___x_1360_ = lean_unbox(v_a_1359_);
lean_dec(v_a_1359_);
if (v___x_1360_ == 0)
{
lean_dec_ref(v___x_1306_);
v___y_1339_ = v___y_1351_;
v___y_1340_ = v___y_1352_;
v___y_1341_ = v___y_1353_;
v___y_1342_ = v___y_1354_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_6857__overap_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
lean_inc_ref(v_toMonadRef_1325_);
v___x_6857__overap_1362_ = l_Lean_addTrace___redArg(v___x_1306_, v___x_1307_, v_toMonadRef_1325_, v___x_1335_, v___x_1328_, v___x_1361_);
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
v___x_1363_ = lean_apply_5(v___x_6857__overap_1362_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, lean_box(0));
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_dec_ref_known(v___x_1363_, 1);
v___y_1339_ = v___y_1351_;
v___y_1340_ = v___y_1352_;
v___y_1341_ = v___y_1353_;
v___y_1342_ = v___y_1354_;
goto v___jp_1338_;
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v___f_1337_);
lean_dec(v_a_1327_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1306_);
v___y_1339_ = v___y_1351_;
v___y_1340_ = v___y_1352_;
v___y_1341_ = v___y_1353_;
v___y_1342_ = v___y_1354_;
goto v___jp_1338_;
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v___f_1337_);
lean_dec(v_a_1327_);
lean_dec_ref(v___x_1306_);
v_a_1372_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1355_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1355_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v___x_1323_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v_k_1261_);
lean_dec_ref(v_positions_1260_);
lean_dec(v_numIndParams_1259_);
lean_dec_ref(v_below_1258_);
v_a_1394_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1326_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1326_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1408_, lean_object* v_numIndParams_1409_, lean_object* v_positions_1410_, lean_object* v_k_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1408_, v_numIndParams_1409_, v_positions_1410_, v_k_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1418_, lean_object* v_inst_1419_, lean_object* v_below_1420_, lean_object* v_numIndParams_1421_, lean_object* v_positions_1422_, lean_object* v_k_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1420_, v_numIndParams_1421_, v_positions_1422_, v_k_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1430_, lean_object* v_inst_1431_, lean_object* v_below_1432_, lean_object* v_numIndParams_1433_, lean_object* v_positions_1434_, lean_object* v_k_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1430_, v_inst_1431_, v_below_1432_, v_numIndParams_1433_, v_positions_1434_, v_k_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_inst_1431_);
return v_res_1441_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(32u);
v___x_1443_ = lean_mk_empty_array_with_capacity(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1445_ = ((size_t)5ULL);
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_unsigned_to_nat(32u);
v___x_1448_ = lean_mk_empty_array_with_capacity(v___x_1447_);
v___x_1449_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1450_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v___x_1448_);
lean_ctor_set(v___x_1450_, 2, v___x_1446_);
lean_ctor_set(v___x_1450_, 3, v___x_1446_);
lean_ctor_set_usize(v___x_1450_, 4, v___x_1445_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v_traceState_1454_; lean_object* v_traces_1455_; lean_object* v___x_1456_; lean_object* v_traceState_1457_; lean_object* v_env_1458_; lean_object* v_nextMacroScope_1459_; lean_object* v_ngen_1460_; lean_object* v_auxDeclNGen_1461_; lean_object* v_cache_1462_; lean_object* v_messages_1463_; lean_object* v_infoState_1464_; lean_object* v_snapshotTasks_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1484_; 
v___x_1453_ = lean_st_ref_get(v___y_1451_);
v_traceState_1454_ = lean_ctor_get(v___x_1453_, 4);
lean_inc_ref(v_traceState_1454_);
lean_dec(v___x_1453_);
v_traces_1455_ = lean_ctor_get(v_traceState_1454_, 0);
lean_inc_ref(v_traces_1455_);
lean_dec_ref(v_traceState_1454_);
v___x_1456_ = lean_st_ref_take(v___y_1451_);
v_traceState_1457_ = lean_ctor_get(v___x_1456_, 4);
v_env_1458_ = lean_ctor_get(v___x_1456_, 0);
v_nextMacroScope_1459_ = lean_ctor_get(v___x_1456_, 1);
v_ngen_1460_ = lean_ctor_get(v___x_1456_, 2);
v_auxDeclNGen_1461_ = lean_ctor_get(v___x_1456_, 3);
v_cache_1462_ = lean_ctor_get(v___x_1456_, 5);
v_messages_1463_ = lean_ctor_get(v___x_1456_, 6);
v_infoState_1464_ = lean_ctor_get(v___x_1456_, 7);
v_snapshotTasks_1465_ = lean_ctor_get(v___x_1456_, 8);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1467_ = v___x_1456_;
v_isShared_1468_ = v_isSharedCheck_1484_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_snapshotTasks_1465_);
lean_inc(v_infoState_1464_);
lean_inc(v_messages_1463_);
lean_inc(v_cache_1462_);
lean_inc(v_traceState_1457_);
lean_inc(v_auxDeclNGen_1461_);
lean_inc(v_ngen_1460_);
lean_inc(v_nextMacroScope_1459_);
lean_inc(v_env_1458_);
lean_dec(v___x_1456_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1484_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
uint64_t v_tid_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1482_; 
v_tid_1469_ = lean_ctor_get_uint64(v_traceState_1457_, sizeof(void*)*1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_traceState_1457_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_traceState_1457_, 0);
lean_dec(v_unused_1483_);
v___x_1471_ = v_traceState_1457_;
v_isShared_1472_ = v_isSharedCheck_1482_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_traceState_1457_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1482_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1473_);
lean_ctor_set_uint64(v_reuseFailAlloc_1481_, sizeof(void*)*1, v_tid_1469_);
v___x_1475_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 4, v___x_1475_);
v___x_1477_ = v___x_1467_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_env_1458_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_nextMacroScope_1459_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_ngen_1460_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_auxDeclNGen_1461_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1480_, 5, v_cache_1462_);
lean_ctor_set(v_reuseFailAlloc_1480_, 6, v_messages_1463_);
lean_ctor_set(v_reuseFailAlloc_1480_, 7, v_infoState_1464_);
lean_ctor_set(v_reuseFailAlloc_1480_, 8, v_snapshotTasks_1465_);
v___x_1477_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_st_ref_put(v___y_1451_, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_traces_1455_);
return v___x_1479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1485_);
lean_dec(v___y_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1500_, lean_object* v_opt_1501_){
_start:
{
lean_object* v_name_1502_; lean_object* v_defValue_1503_; lean_object* v_map_1504_; lean_object* v___x_1505_; 
v_name_1502_ = lean_ctor_get(v_opt_1501_, 0);
v_defValue_1503_ = lean_ctor_get(v_opt_1501_, 1);
v_map_1504_ = lean_ctor_get(v_opts_1500_, 0);
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1504_, v_name_1502_);
if (lean_obj_tag(v___x_1505_) == 0)
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_unbox(v_defValue_1503_);
return v___x_1506_;
}
else
{
lean_object* v_val_1507_; 
v_val_1507_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v___x_1505_, 1);
if (lean_obj_tag(v_val_1507_) == 1)
{
uint8_t v_v_1508_; 
v_v_1508_ = lean_ctor_get_uint8(v_val_1507_, 0);
lean_dec_ref_known(v_val_1507_, 0);
return v_v_1508_;
}
else
{
uint8_t v___x_1509_; 
lean_dec(v_val_1507_);
v___x_1509_ = lean_unbox(v_defValue_1503_);
return v___x_1509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1510_, lean_object* v_opt_1511_){
_start:
{
uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_res_1512_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1510_, v_opt_1511_);
lean_dec_ref(v_opt_1511_);
lean_dec_ref(v_opts_1510_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1514_, lean_object* v_fnIndex_1515_, lean_object* v_recArg_1516_, lean_object* v_below_1517_, lean_object* v_Cs_1518_, lean_object* v_belowDict_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_array_get_borrowed(v___x_1514_, v_Cs_1518_, v_fnIndex_1515_);
lean_inc(v___x_1525_);
v___x_1526_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1525_, v_belowDict_1519_, v_recArg_1516_, v_below_1517_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1527_, lean_object* v_fnIndex_1528_, lean_object* v_recArg_1529_, lean_object* v_below_1530_, lean_object* v_Cs_1531_, lean_object* v_belowDict_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1527_, v_fnIndex_1528_, v_recArg_1529_, v_below_1530_, v_Cs_1531_, v_belowDict_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v_Cs_1531_);
lean_dec(v_fnIndex_1528_);
lean_dec_ref(v___x_1527_);
return v_res_1538_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1545_, lean_object* v_recArg_1546_, lean_object* v_x_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
v___x_1553_ = lean_infer_type(v_below_1545_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1568_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1568_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1568_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1559_ = l_Lean_MessageData_ofExpr(v_recArg_1546_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_MessageData_ofExpr(v_a_1554_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1564_);
v___x_1566_ = v___x_1556_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v_recArg_1546_);
v_a_1569_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1553_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1553_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1577_, lean_object* v_recArg_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1577_, v_recArg_1578_, v_x_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v_x_1579_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t v_sz_1586_, size_t v_i_1587_, lean_object* v_bs_1588_){
_start:
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_usize_dec_lt(v_i_1587_, v_sz_1586_);
if (v___x_1589_ == 0)
{
return v_bs_1588_;
}
else
{
lean_object* v_v_1590_; lean_object* v_msg_1591_; lean_object* v___x_1592_; lean_object* v_bs_x27_1593_; size_t v___x_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v_v_1590_ = lean_array_uget_borrowed(v_bs_1588_, v_i_1587_);
v_msg_1591_ = lean_ctor_get(v_v_1590_, 1);
lean_inc_ref(v_msg_1591_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v_bs_x27_1593_ = lean_array_uset(v_bs_1588_, v_i_1587_, v___x_1592_);
v___x_1594_ = ((size_t)1ULL);
v___x_1595_ = lean_usize_add(v_i_1587_, v___x_1594_);
v___x_1596_ = lean_array_uset(v_bs_x27_1593_, v_i_1587_, v_msg_1591_);
v_i_1587_ = v___x_1595_;
v_bs_1588_ = v___x_1596_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1598_, lean_object* v_i_1599_, lean_object* v_bs_1600_){
_start:
{
size_t v_sz_boxed_1601_; size_t v_i_boxed_1602_; lean_object* v_res_1603_; 
v_sz_boxed_1601_ = lean_unbox_usize(v_sz_1598_);
lean_dec(v_sz_1598_);
v_i_boxed_1602_ = lean_unbox_usize(v_i_1599_);
lean_dec(v_i_1599_);
v_res_1603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_boxed_1601_, v_i_boxed_1602_, v_bs_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_oldTraces_1604_, lean_object* v_data_1605_, lean_object* v_ref_1606_, lean_object* v_msg_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_toCold_1613_; lean_object* v_currRecDepth_1614_; lean_object* v_ref_1615_; uint8_t v_diag_1616_; uint8_t v_suppressElabErrors_1617_; lean_object* v___x_1618_; lean_object* v_traceState_1619_; lean_object* v_traces_1620_; lean_object* v_ref_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; size_t v_sz_1624_; size_t v___x_1625_; lean_object* v___x_1626_; lean_object* v_msg_1627_; lean_object* v___x_1628_; lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1666_; 
v_toCold_1613_ = lean_ctor_get(v___y_1610_, 0);
v_currRecDepth_1614_ = lean_ctor_get(v___y_1610_, 1);
v_ref_1615_ = lean_ctor_get(v___y_1610_, 2);
v_diag_1616_ = lean_ctor_get_uint8(v___y_1610_, sizeof(void*)*3);
v_suppressElabErrors_1617_ = lean_ctor_get_uint8(v___y_1610_, sizeof(void*)*3 + 1);
v___x_1618_ = lean_st_ref_get(v___y_1611_);
v_traceState_1619_ = lean_ctor_get(v___x_1618_, 4);
lean_inc_ref(v_traceState_1619_);
lean_dec(v___x_1618_);
v_traces_1620_ = lean_ctor_get(v_traceState_1619_, 0);
lean_inc_ref(v_traces_1620_);
lean_dec_ref(v_traceState_1619_);
v_ref_1621_ = l_Lean_replaceRef(v_ref_1606_, v_ref_1615_);
lean_inc(v_currRecDepth_1614_);
lean_inc_ref(v_toCold_1613_);
v___x_1622_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1622_, 0, v_toCold_1613_);
lean_ctor_set(v___x_1622_, 1, v_currRecDepth_1614_);
lean_ctor_set(v___x_1622_, 2, v_ref_1621_);
lean_ctor_set_uint8(v___x_1622_, sizeof(void*)*3, v_diag_1616_);
lean_ctor_set_uint8(v___x_1622_, sizeof(void*)*3 + 1, v_suppressElabErrors_1617_);
v___x_1623_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1620_);
lean_dec_ref(v_traces_1620_);
v_sz_1624_ = lean_array_size(v___x_1623_);
v___x_1625_ = ((size_t)0ULL);
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1624_, v___x_1625_, v___x_1623_);
v_msg_1627_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1627_, 0, v_data_1605_);
lean_ctor_set(v_msg_1627_, 1, v_msg_1607_);
lean_ctor_set(v_msg_1627_, 2, v___x_1626_);
v___x_1628_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1627_, v___y_1608_, v___y_1609_, v___x_1622_, v___y_1611_);
lean_dec_ref_known(v___x_1622_, 3);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1666_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1666_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v_traceState_1634_; lean_object* v_env_1635_; lean_object* v_nextMacroScope_1636_; lean_object* v_ngen_1637_; lean_object* v_auxDeclNGen_1638_; lean_object* v_cache_1639_; lean_object* v_messages_1640_; lean_object* v_infoState_1641_; lean_object* v_snapshotTasks_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1665_; 
v___x_1633_ = lean_st_ref_take(v___y_1611_);
v_traceState_1634_ = lean_ctor_get(v___x_1633_, 4);
v_env_1635_ = lean_ctor_get(v___x_1633_, 0);
v_nextMacroScope_1636_ = lean_ctor_get(v___x_1633_, 1);
v_ngen_1637_ = lean_ctor_get(v___x_1633_, 2);
v_auxDeclNGen_1638_ = lean_ctor_get(v___x_1633_, 3);
v_cache_1639_ = lean_ctor_get(v___x_1633_, 5);
v_messages_1640_ = lean_ctor_get(v___x_1633_, 6);
v_infoState_1641_ = lean_ctor_get(v___x_1633_, 7);
v_snapshotTasks_1642_ = lean_ctor_get(v___x_1633_, 8);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1644_ = v___x_1633_;
v_isShared_1645_ = v_isSharedCheck_1665_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_snapshotTasks_1642_);
lean_inc(v_infoState_1641_);
lean_inc(v_messages_1640_);
lean_inc(v_cache_1639_);
lean_inc(v_traceState_1634_);
lean_inc(v_auxDeclNGen_1638_);
lean_inc(v_ngen_1637_);
lean_inc(v_nextMacroScope_1636_);
lean_inc(v_env_1635_);
lean_dec(v___x_1633_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1665_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
uint64_t v_tid_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1663_; 
v_tid_1646_ = lean_ctor_get_uint64(v_traceState_1634_, sizeof(void*)*1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_traceState_1634_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v_traceState_1634_, 0);
lean_dec(v_unused_1664_);
v___x_1648_ = v_traceState_1634_;
v_isShared_1649_ = v_isSharedCheck_1663_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v_traceState_1634_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1663_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_ref_1606_);
lean_ctor_set(v___x_1650_, 1, v_a_1629_);
v___x_1651_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1604_, v___x_1650_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1651_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1651_);
lean_ctor_set_uint64(v_reuseFailAlloc_1662_, sizeof(void*)*1, v_tid_1646_);
v___x_1653_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 4, v___x_1653_);
v___x_1655_ = v___x_1644_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_env_1635_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_nextMacroScope_1636_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_ngen_1637_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_auxDeclNGen_1638_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1661_, 5, v_cache_1639_);
lean_ctor_set(v_reuseFailAlloc_1661_, 6, v_messages_1640_);
lean_ctor_set(v_reuseFailAlloc_1661_, 7, v_infoState_1641_);
lean_ctor_set(v_reuseFailAlloc_1661_, 8, v_snapshotTasks_1642_);
v___x_1655_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1656_ = lean_st_ref_put(v___y_1611_, v___x_1655_);
v___x_1657_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1657_);
v___x_1659_ = v___x_1631_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1667_, lean_object* v_data_1668_, lean_object* v_ref_1669_, lean_object* v_msg_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1667_, v_data_1668_, v_ref_1669_, v_msg_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1677_, lean_object* v_opt_1678_){
_start:
{
lean_object* v_name_1679_; lean_object* v_defValue_1680_; lean_object* v_map_1681_; lean_object* v___x_1682_; 
v_name_1679_ = lean_ctor_get(v_opt_1678_, 0);
v_defValue_1680_ = lean_ctor_get(v_opt_1678_, 1);
v_map_1681_ = lean_ctor_get(v_opts_1677_, 0);
v___x_1682_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1681_, v_name_1679_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_inc(v_defValue_1680_);
return v_defValue_1680_;
}
else
{
lean_object* v_val_1683_; 
v_val_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v___x_1682_, 1);
if (lean_obj_tag(v_val_1683_) == 3)
{
lean_object* v_v_1684_; 
v_v_1684_ = lean_ctor_get(v_val_1683_, 0);
lean_inc(v_v_1684_);
lean_dec_ref_known(v_val_1683_, 1);
return v_v_1684_;
}
else
{
lean_dec(v_val_1683_);
lean_inc(v_defValue_1680_);
return v_defValue_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1685_, lean_object* v_opt_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1685_, v_opt_1686_);
lean_dec_ref(v_opt_1686_);
lean_dec_ref(v_opts_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1688_){
_start:
{
if (lean_obj_tag(v_e_1688_) == 0)
{
uint8_t v___x_1689_; 
v___x_1689_ = 2;
return v___x_1689_;
}
else
{
lean_object* v_a_1690_; uint8_t v___x_1691_; 
v_a_1690_ = lean_ctor_get(v_e_1688_, 0);
v___x_1691_ = l_Lean_Expr_hasSyntheticSorry(v_a_1690_);
if (v___x_1691_ == 0)
{
uint8_t v___x_1692_; 
v___x_1692_ = 0;
return v___x_1692_;
}
else
{
uint8_t v___x_1693_; 
v___x_1693_ = 1;
return v___x_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1694_);
lean_dec_ref(v_e_1694_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
v_a_1699_ = lean_ctor_get(v_x_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v_x_1697_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v_x_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 1);
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1707_ = lean_ctor_get(v_x_1697_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v_x_1697_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v_x_1697_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 0);
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1715_);
return v_res_1717_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1721_; double v___x_1722_; 
v___x_1721_ = lean_unsigned_to_nat(1000u);
v___x_1722_ = lean_float_of_nat(v___x_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1723_, uint8_t v_collapsed_1724_, lean_object* v_tag_1725_, lean_object* v_opts_1726_, uint8_t v_clsEnabled_1727_, lean_object* v_oldTraces_1728_, lean_object* v_msg_1729_, lean_object* v_resStartStop_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_fst_1736_; lean_object* v_snd_1737_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v_data_1741_; lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___y_1757_; lean_object* v_a_1758_; uint8_t v___y_1773_; double v___y_1804_; 
v_fst_1736_ = lean_ctor_get(v_resStartStop_1730_, 0);
lean_inc(v_fst_1736_);
v_snd_1737_ = lean_ctor_get(v_resStartStop_1730_, 1);
lean_inc(v_snd_1737_);
lean_dec_ref(v_resStartStop_1730_);
v_fst_1752_ = lean_ctor_get(v_snd_1737_, 0);
lean_inc(v_fst_1752_);
v_snd_1753_ = lean_ctor_get(v_snd_1737_, 1);
lean_inc(v_snd_1753_);
lean_dec(v_snd_1737_);
v___x_1754_ = l_Lean_trace_profiler;
v___x_1755_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1726_, v___x_1754_);
if (v___x_1755_ == 0)
{
v___y_1773_ = v___x_1755_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1810_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1726_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; double v___x_1813_; double v___x_1814_; double v___x_1815_; 
v___x_1811_ = l_Lean_trace_profiler_threshold;
v___x_1812_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1726_, v___x_1811_);
v___x_1813_ = lean_float_of_nat(v___x_1812_);
v___x_1814_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2);
v___x_1815_ = lean_float_div(v___x_1813_, v___x_1814_);
v___y_1804_ = v___x_1815_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; double v___x_1818_; 
v___x_1816_ = l_Lean_trace_profiler_threshold;
v___x_1817_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1726_, v___x_1816_);
v___x_1818_ = lean_float_of_nat(v___x_1817_);
v___y_1804_ = v___x_1818_;
goto v___jp_1803_;
}
}
v___jp_1738_:
{
lean_object* v___x_1742_; 
lean_inc(v___y_1740_);
v___x_1742_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1728_, v_data_1741_, v___y_1740_, v___y_1739_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1743_; 
lean_dec_ref_known(v___x_1742_, 1);
v___x_1743_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1736_);
return v___x_1743_;
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v_fst_1736_);
v_a_1744_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1742_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1742_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
v___jp_1756_:
{
uint8_t v_result_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; double v___x_1762_; lean_object* v_data_1763_; 
v_result_1759_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1736_);
v___x_1760_ = lean_box(v_result_1759_);
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
v___x_1762_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1725_);
lean_inc_ref(v___x_1761_);
lean_inc(v_cls_1723_);
v_data_1763_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1763_, 0, v_cls_1723_);
lean_ctor_set(v_data_1763_, 1, v___x_1761_);
lean_ctor_set(v_data_1763_, 2, v_tag_1725_);
lean_ctor_set_float(v_data_1763_, sizeof(void*)*3, v___x_1762_);
lean_ctor_set_float(v_data_1763_, sizeof(void*)*3 + 8, v___x_1762_);
lean_ctor_set_uint8(v_data_1763_, sizeof(void*)*3 + 16, v_collapsed_1724_);
if (v___x_1755_ == 0)
{
lean_dec_ref_known(v___x_1761_, 1);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_dec_ref(v_tag_1725_);
lean_dec(v_cls_1723_);
v___y_1739_ = v_a_1758_;
v___y_1740_ = v___y_1757_;
v_data_1741_ = v_data_1763_;
goto v___jp_1738_;
}
else
{
lean_object* v_data_1764_; double v___x_1765_; double v___x_1766_; 
lean_dec_ref_known(v_data_1763_, 3);
v_data_1764_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1764_, 0, v_cls_1723_);
lean_ctor_set(v_data_1764_, 1, v___x_1761_);
lean_ctor_set(v_data_1764_, 2, v_tag_1725_);
v___x_1765_ = lean_unbox_float(v_fst_1752_);
lean_dec(v_fst_1752_);
lean_ctor_set_float(v_data_1764_, sizeof(void*)*3, v___x_1765_);
v___x_1766_ = lean_unbox_float(v_snd_1753_);
lean_dec(v_snd_1753_);
lean_ctor_set_float(v_data_1764_, sizeof(void*)*3 + 8, v___x_1766_);
lean_ctor_set_uint8(v_data_1764_, sizeof(void*)*3 + 16, v_collapsed_1724_);
v___y_1739_ = v_a_1758_;
v___y_1740_ = v___y_1757_;
v_data_1741_ = v_data_1764_;
goto v___jp_1738_;
}
}
v___jp_1767_:
{
lean_object* v_ref_1768_; lean_object* v___x_1769_; 
v_ref_1768_ = lean_ctor_get(v___y_1733_, 2);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v_fst_1736_);
v___x_1769_ = lean_apply_6(v_msg_1729_, v_fst_1736_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, lean_box(0));
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___y_1757_ = v_ref_1768_;
v_a_1758_ = v_a_1770_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1771_; 
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
v___y_1757_ = v_ref_1768_;
v_a_1758_ = v___x_1771_;
goto v___jp_1756_;
}
}
v___jp_1772_:
{
if (v_clsEnabled_1727_ == 0)
{
if (v___y_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v_traceState_1775_; lean_object* v_env_1776_; lean_object* v_nextMacroScope_1777_; lean_object* v_ngen_1778_; lean_object* v_auxDeclNGen_1779_; lean_object* v_cache_1780_; lean_object* v_messages_1781_; lean_object* v_infoState_1782_; lean_object* v_snapshotTasks_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_dec_ref(v_msg_1729_);
lean_dec_ref(v_tag_1725_);
lean_dec(v_cls_1723_);
v___x_1774_ = lean_st_ref_take(v___y_1734_);
v_traceState_1775_ = lean_ctor_get(v___x_1774_, 4);
v_env_1776_ = lean_ctor_get(v___x_1774_, 0);
v_nextMacroScope_1777_ = lean_ctor_get(v___x_1774_, 1);
v_ngen_1778_ = lean_ctor_get(v___x_1774_, 2);
v_auxDeclNGen_1779_ = lean_ctor_get(v___x_1774_, 3);
v_cache_1780_ = lean_ctor_get(v___x_1774_, 5);
v_messages_1781_ = lean_ctor_get(v___x_1774_, 6);
v_infoState_1782_ = lean_ctor_get(v___x_1774_, 7);
v_snapshotTasks_1783_ = lean_ctor_get(v___x_1774_, 8);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1785_ = v___x_1774_;
v_isShared_1786_ = v_isSharedCheck_1802_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_snapshotTasks_1783_);
lean_inc(v_infoState_1782_);
lean_inc(v_messages_1781_);
lean_inc(v_cache_1780_);
lean_inc(v_traceState_1775_);
lean_inc(v_auxDeclNGen_1779_);
lean_inc(v_ngen_1778_);
lean_inc(v_nextMacroScope_1777_);
lean_inc(v_env_1776_);
lean_dec(v___x_1774_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1802_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
uint64_t v_tid_1787_; lean_object* v_traces_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1801_; 
v_tid_1787_ = lean_ctor_get_uint64(v_traceState_1775_, sizeof(void*)*1);
v_traces_1788_ = lean_ctor_get(v_traceState_1775_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_traceState_1775_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1790_ = v_traceState_1775_;
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_traces_1788_);
lean_dec(v_traceState_1775_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1728_, v_traces_1788_);
lean_dec_ref(v_traces_1788_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1792_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1792_);
lean_ctor_set_uint64(v_reuseFailAlloc_1800_, sizeof(void*)*1, v_tid_1787_);
v___x_1794_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 4, v___x_1794_);
v___x_1796_ = v___x_1785_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_env_1776_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_nextMacroScope_1777_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_ngen_1778_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_auxDeclNGen_1779_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_cache_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_messages_1781_);
lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_infoState_1782_);
lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_snapshotTasks_1783_);
v___x_1796_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_st_ref_put(v___y_1734_, v___x_1796_);
v___x_1798_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1736_);
return v___x_1798_;
}
}
}
}
}
else
{
goto v___jp_1767_;
}
}
else
{
goto v___jp_1767_;
}
}
v___jp_1803_:
{
double v___x_1805_; double v___x_1806_; double v___x_1807_; uint8_t v___x_1808_; 
v___x_1805_ = lean_unbox_float(v_snd_1753_);
v___x_1806_ = lean_unbox_float(v_fst_1752_);
v___x_1807_ = lean_float_sub(v___x_1805_, v___x_1806_);
v___x_1808_ = lean_float_decLt(v___y_1804_, v___x_1807_);
v___y_1773_ = v___x_1808_;
goto v___jp_1772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1819_, lean_object* v_collapsed_1820_, lean_object* v_tag_1821_, lean_object* v_opts_1822_, lean_object* v_clsEnabled_1823_, lean_object* v_oldTraces_1824_, lean_object* v_msg_1825_, lean_object* v_resStartStop_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
uint8_t v_collapsed_boxed_1832_; uint8_t v_clsEnabled_boxed_1833_; lean_object* v_res_1834_; 
v_collapsed_boxed_1832_ = lean_unbox(v_collapsed_1820_);
v_clsEnabled_boxed_1833_ = lean_unbox(v_clsEnabled_1823_);
v_res_1834_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1819_, v_collapsed_boxed_1832_, v_tag_1821_, v_opts_1822_, v_clsEnabled_boxed_1833_, v_oldTraces_1824_, v_msg_1825_, v_resStartStop_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_opts_1822_);
return v_res_1834_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1836_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1837_ = l_Lean_Name_append(v___x_1836_, v___x_1835_);
return v___x_1837_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__1(void){
_start:
{
lean_object* v___x_1838_; double v___x_1839_; 
v___x_1838_ = lean_unsigned_to_nat(1000000000u);
v___x_1839_ = lean_float_of_nat(v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1840_, lean_object* v_numIndParams_1841_, lean_object* v_positions_1842_, lean_object* v_fnIndex_1843_, lean_object* v_recArg_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_toCold_1850_; lean_object* v_options_1851_; lean_object* v_inheritedTraceOptions_1852_; uint8_t v_hasTrace_1853_; lean_object* v___x_1854_; lean_object* v___f_1855_; 
v_toCold_1850_ = lean_ctor_get(v_a_1847_, 0);
v_options_1851_ = lean_ctor_get(v_toCold_1850_, 2);
v_inheritedTraceOptions_1852_ = lean_ctor_get(v_toCold_1850_, 11);
v_hasTrace_1853_ = lean_ctor_get_uint8(v_options_1851_, sizeof(void*)*1);
v___x_1854_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1840_);
lean_inc_ref(v_recArg_1844_);
v___f_1855_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1855_, 0, v___x_1854_);
lean_closure_set(v___f_1855_, 1, v_fnIndex_1843_);
lean_closure_set(v___f_1855_, 2, v_recArg_1844_);
lean_closure_set(v___f_1855_, 3, v_below_1840_);
if (v_hasTrace_1853_ == 0)
{
lean_object* v___x_1856_; 
lean_dec_ref(v_recArg_1844_);
v___x_1856_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1840_, v_numIndParams_1841_, v_positions_1842_, v___f_1855_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
return v___x_1856_;
}
else
{
lean_object* v___f_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v_a_1865_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v_a_1880_; 
lean_inc_ref(v_below_1840_);
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1857_, 0, v_below_1840_);
lean_closure_set(v___f_1857_, 1, v_recArg_1844_);
v___x_1858_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1859_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1860_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1861_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1852_, v_options_1851_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = l_Lean_trace_profiler;
v___x_1931_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1851_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref(v___f_1857_);
v___x_1932_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1840_, v_numIndParams_1841_, v_positions_1842_, v___f_1855_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
return v___x_1932_;
}
else
{
goto v___jp_1889_;
}
}
else
{
goto v___jp_1889_;
}
v___jp_1862_:
{
lean_object* v___x_1866_; double v___x_1867_; double v___x_1868_; double v___x_1869_; double v___x_1870_; double v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1866_ = lean_io_mono_nanos_now();
v___x_1867_ = lean_float_of_nat(v___y_1864_);
v___x_1868_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__1, &l_Lean_Elab_Structural_toBelow___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___closed__1);
v___x_1869_ = lean_float_div(v___x_1867_, v___x_1868_);
v___x_1870_ = lean_float_of_nat(v___x_1866_);
v___x_1871_ = lean_float_div(v___x_1870_, v___x_1868_);
v___x_1872_ = lean_box_float(v___x_1869_);
v___x_1873_ = lean_box_float(v___x_1871_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_a_1865_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1858_, v_hasTrace_1853_, v___x_1859_, v_options_1851_, v___x_1861_, v___y_1863_, v___f_1857_, v___x_1875_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
return v___x_1876_;
}
v___jp_1877_:
{
lean_object* v___x_1881_; double v___x_1882_; double v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1881_ = lean_io_get_num_heartbeats();
v___x_1882_ = lean_float_of_nat(v___y_1878_);
v___x_1883_ = lean_float_of_nat(v___x_1881_);
v___x_1884_ = lean_box_float(v___x_1882_);
v___x_1885_ = lean_box_float(v___x_1883_);
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v_a_1880_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1858_, v_hasTrace_1853_, v___x_1859_, v_options_1851_, v___x_1861_, v___y_1879_, v___f_1857_, v___x_1887_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
return v___x_1888_;
}
v___jp_1889_:
{
lean_object* v___x_1890_; lean_object* v_a_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1890_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1848_);
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref(v___x_1890_);
v___x_1892_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1893_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1851_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_io_mono_nanos_now();
v___x_1895_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1840_, v_numIndParams_1841_, v_positions_1842_, v___f_1855_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set_tag(v___x_1898_, 1);
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v___y_1863_ = v_a_1891_;
v___y_1864_ = v___x_1894_;
v_a_1865_ = v___x_1901_;
goto v___jp_1862_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_a_1904_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1895_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1895_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 0);
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
v___y_1863_ = v_a_1891_;
v___y_1864_ = v___x_1894_;
v_a_1865_ = v___x_1909_;
goto v___jp_1862_;
}
}
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_io_get_num_heartbeats();
v___x_1913_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1840_, v_numIndParams_1841_, v_positions_1842_, v___f_1855_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
v___y_1878_ = v___x_1912_;
v___y_1879_ = v_a_1891_;
v_a_1880_ = v___x_1919_;
goto v___jp_1877_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set_tag(v___x_1924_, 0);
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
v___y_1878_ = v___x_1912_;
v___y_1879_ = v_a_1891_;
v_a_1880_ = v___x_1927_;
goto v___jp_1877_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1933_, lean_object* v_numIndParams_1934_, lean_object* v_positions_1935_, lean_object* v_fnIndex_1936_, lean_object* v_recArg_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Elab_Structural_toBelow(v_below_1933_, v_numIndParams_1934_, v_positions_1935_, v_fnIndex_1936_, v_recArg_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1944_, lean_object* v_x_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1945_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1952_, v_x_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1960_, lean_object* v___y_1961_, lean_object* v_b_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
lean_inc(v___y_1966_);
lean_inc_ref(v___y_1965_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
lean_inc(v___y_1961_);
v___x_1968_ = lean_apply_7(v_k_1960_, v_b_1962_, v___y_1961_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, lean_box(0));
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_1969_, lean_object* v___y_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_1969_, v___y_1970_, v_b_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1970_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_1978_, uint8_t v_bi_1979_, lean_object* v_type_1980_, lean_object* v_k_1981_, uint8_t v_kind_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___f_1989_; lean_object* v___x_1990_; 
lean_inc(v___y_1983_);
v___f_1989_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1989_, 0, v_k_1981_);
lean_closure_set(v___f_1989_, 1, v___y_1983_);
v___x_1990_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1978_, v_bi_1979_, v_type_1980_, v___f_1989_, v_kind_1982_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_1990_) == 0)
{
return v___x_1990_;
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_1999_, lean_object* v_bi_2000_, lean_object* v_type_2001_, lean_object* v_k_2002_, lean_object* v_kind_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
uint8_t v_bi_boxed_2010_; uint8_t v_kind_boxed_2011_; lean_object* v_res_2012_; 
v_bi_boxed_2010_ = lean_unbox(v_bi_2000_);
v_kind_boxed_2011_ = lean_unbox(v_kind_2003_);
v_res_2012_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_1999_, v_bi_boxed_2010_, v_type_2001_, v_k_2002_, v_kind_boxed_2011_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2013_, lean_object* v_name_2014_, uint8_t v_bi_2015_, lean_object* v_type_2016_, lean_object* v_k_2017_, uint8_t v_kind_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2014_, v_bi_2015_, v_type_2016_, v_k_2017_, v_kind_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2026_, lean_object* v_name_2027_, lean_object* v_bi_2028_, lean_object* v_type_2029_, lean_object* v_k_2030_, lean_object* v_kind_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
uint8_t v_bi_boxed_2038_; uint8_t v_kind_boxed_2039_; lean_object* v_res_2040_; 
v_bi_boxed_2038_ = lean_unbox(v_bi_2028_);
v_kind_boxed_2039_ = lean_unbox(v_kind_2031_);
v_res_2040_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2026_, v_name_2027_, v_bi_boxed_2038_, v_type_2029_, v_k_2030_, v_kind_boxed_2039_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2041_, lean_object* v___y_2042_, lean_object* v_b_2043_, lean_object* v_c_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
lean_inc(v___y_2042_);
v___x_2050_ = lean_apply_8(v_k_2041_, v_b_2043_, v_c_2044_, v___y_2042_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, lean_box(0));
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2051_, lean_object* v___y_2052_, lean_object* v_b_2053_, lean_object* v_c_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2051_, v___y_2052_, v_b_2053_, v_c_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2052_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2061_, lean_object* v_maxFVars_2062_, lean_object* v_k_2063_, uint8_t v_cleanupAnnotations_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___f_2071_; uint8_t v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_inc(v___y_2065_);
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2071_, 0, v_k_2063_);
lean_closure_set(v___f_2071_, 1, v___y_2065_);
v___x_2072_ = 1;
v___x_2073_ = 0;
v___x_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_maxFVars_2062_);
v___x_2075_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2061_, v___x_2072_, v___x_2073_, v___x_2072_, v___x_2073_, v___x_2074_, v___f_2071_, v_cleanupAnnotations_2064_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec_ref_known(v___x_2074_, 1);
if (lean_obj_tag(v___x_2075_) == 0)
{
return v___x_2075_;
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2084_, lean_object* v_maxFVars_2085_, lean_object* v_k_2086_, lean_object* v_cleanupAnnotations_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2094_; lean_object* v_res_2095_; 
v_cleanupAnnotations_boxed_2094_ = lean_unbox(v_cleanupAnnotations_2087_);
v_res_2095_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2084_, v_maxFVars_2085_, v_k_2086_, v_cleanupAnnotations_boxed_2094_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2096_, lean_object* v_e_2097_, lean_object* v_maxFVars_2098_, lean_object* v_k_2099_, uint8_t v_cleanupAnnotations_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2097_, v_maxFVars_2098_, v_k_2099_, v_cleanupAnnotations_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_e_2109_, lean_object* v_maxFVars_2110_, lean_object* v_k_2111_, lean_object* v_cleanupAnnotations_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2119_; lean_object* v_res_2120_; 
v_cleanupAnnotations_boxed_2119_ = lean_unbox(v_cleanupAnnotations_2112_);
v_res_2120_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2108_, v_e_2109_, v_maxFVars_2110_, v_k_2111_, v_cleanupAnnotations_boxed_2119_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2121_, lean_object* v_msg_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_ref_2128_; lean_object* v___x_2129_; lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2174_; 
v_ref_2128_ = lean_ctor_get(v___y_2125_, 2);
v___x_2129_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2174_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2174_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v_traceState_2135_; lean_object* v_env_2136_; lean_object* v_nextMacroScope_2137_; lean_object* v_ngen_2138_; lean_object* v_auxDeclNGen_2139_; lean_object* v_cache_2140_; lean_object* v_messages_2141_; lean_object* v_infoState_2142_; lean_object* v_snapshotTasks_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2173_; 
v___x_2134_ = lean_st_ref_take(v___y_2126_);
v_traceState_2135_ = lean_ctor_get(v___x_2134_, 4);
v_env_2136_ = lean_ctor_get(v___x_2134_, 0);
v_nextMacroScope_2137_ = lean_ctor_get(v___x_2134_, 1);
v_ngen_2138_ = lean_ctor_get(v___x_2134_, 2);
v_auxDeclNGen_2139_ = lean_ctor_get(v___x_2134_, 3);
v_cache_2140_ = lean_ctor_get(v___x_2134_, 5);
v_messages_2141_ = lean_ctor_get(v___x_2134_, 6);
v_infoState_2142_ = lean_ctor_get(v___x_2134_, 7);
v_snapshotTasks_2143_ = lean_ctor_get(v___x_2134_, 8);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2145_ = v___x_2134_;
v_isShared_2146_ = v_isSharedCheck_2173_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_snapshotTasks_2143_);
lean_inc(v_infoState_2142_);
lean_inc(v_messages_2141_);
lean_inc(v_cache_2140_);
lean_inc(v_traceState_2135_);
lean_inc(v_auxDeclNGen_2139_);
lean_inc(v_ngen_2138_);
lean_inc(v_nextMacroScope_2137_);
lean_inc(v_env_2136_);
lean_dec(v___x_2134_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2173_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
uint64_t v_tid_2147_; lean_object* v_traces_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2172_; 
v_tid_2147_ = lean_ctor_get_uint64(v_traceState_2135_, sizeof(void*)*1);
v_traces_2148_ = lean_ctor_get(v_traceState_2135_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_traceState_2135_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2150_ = v_traceState_2135_;
v_isShared_2151_ = v_isSharedCheck_2172_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_traces_2148_);
lean_dec(v_traceState_2135_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2172_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; double v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2154_ = 0;
v___x_2155_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2156_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2156_, 0, v_cls_2121_);
lean_ctor_set(v___x_2156_, 1, v___x_2152_);
lean_ctor_set(v___x_2156_, 2, v___x_2155_);
lean_ctor_set_float(v___x_2156_, sizeof(void*)*3, v___x_2153_);
lean_ctor_set_float(v___x_2156_, sizeof(void*)*3 + 8, v___x_2153_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*3 + 16, v___x_2154_);
v___x_2157_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2158_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v_a_2130_);
lean_ctor_set(v___x_2158_, 2, v___x_2157_);
lean_inc(v_ref_2128_);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_ref_2128_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Lean_PersistentArray_push___redArg(v_traces_2148_, v___x_2159_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2160_);
v___x_2162_ = v___x_2150_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2160_);
lean_ctor_set_uint64(v_reuseFailAlloc_2171_, sizeof(void*)*1, v_tid_2147_);
v___x_2162_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 4, v___x_2162_);
v___x_2164_ = v___x_2145_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_env_2136_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_nextMacroScope_2137_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_ngen_2138_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_auxDeclNGen_2139_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2170_, 5, v_cache_2140_);
lean_ctor_set(v_reuseFailAlloc_2170_, 6, v_messages_2141_);
lean_ctor_set(v_reuseFailAlloc_2170_, 7, v_infoState_2142_);
lean_ctor_set(v_reuseFailAlloc_2170_, 8, v_snapshotTasks_2143_);
v___x_2164_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = lean_st_ref_put(v___y_2126_, v___x_2164_);
v___x_2166_ = lean_box(0);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2166_);
v___x_2168_ = v___x_2132_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2175_, lean_object* v_msg_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2175_, v_msg_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2183_, lean_object* v_as_2184_, size_t v_i_2185_, size_t v_stop_2186_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = lean_usize_dec_eq(v_i_2185_, v_stop_2186_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v_fnName_2193_; lean_object* v_recArgPos_2194_; uint8_t v___x_2195_; 
v___x_2192_ = lean_array_uget_borrowed(v_as_2184_, v_i_2185_);
v_fnName_2193_ = lean_ctor_get(v___x_2192_, 0);
v_recArgPos_2194_ = lean_ctor_get(v___x_2192_, 2);
lean_inc(v_recArgPos_2194_);
lean_inc(v_fnName_2193_);
v___x_2195_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2193_, v_recArgPos_2194_, v_e_2183_);
if (v___x_2195_ == 0)
{
goto v___jp_2187_;
}
else
{
if (v___x_2195_ == 0)
{
goto v___jp_2187_;
}
else
{
return v___x_2195_;
}
}
}
else
{
uint8_t v___x_2196_; 
v___x_2196_ = 0;
return v___x_2196_;
}
v___jp_2187_:
{
size_t v___x_2188_; size_t v___x_2189_; 
v___x_2188_ = ((size_t)1ULL);
v___x_2189_ = lean_usize_add(v_i_2185_, v___x_2188_);
v_i_2185_ = v___x_2189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2197_, lean_object* v_as_2198_, lean_object* v_i_2199_, lean_object* v_stop_2200_){
_start:
{
size_t v_i_boxed_2201_; size_t v_stop_boxed_2202_; uint8_t v_res_2203_; lean_object* v_r_2204_; 
v_i_boxed_2201_ = lean_unbox_usize(v_i_2199_);
lean_dec(v_i_2199_);
v_stop_boxed_2202_ = lean_unbox_usize(v_stop_2200_);
lean_dec(v_stop_2200_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2197_, v_as_2198_, v_i_boxed_2201_, v_stop_boxed_2202_);
lean_dec_ref(v_as_2198_);
lean_dec_ref(v_e_2197_);
v_r_2204_ = lean_box(v_res_2203_);
return v_r_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2205_, lean_object* v_____do__lift_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_toCold_2213_; lean_object* v_options_2214_; uint8_t v_hasTrace_2215_; 
v_toCold_2213_ = lean_ctor_get(v___y_2210_, 0);
v_options_2214_ = lean_ctor_get(v_toCold_2213_, 2);
v_hasTrace_2215_ = lean_ctor_get_uint8(v_options_2214_, sizeof(void*)*1);
if (v_hasTrace_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v___x_2205_);
v___x_2216_ = lean_box(v_hasTrace_2215_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
return v___x_2217_;
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2219_ = l_Lean_Name_append(v___x_2218_, v___x_2205_);
v___x_2220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2206_, v_options_2214_, v___x_2219_);
lean_dec(v___x_2219_);
v___x_2221_ = lean_box(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2223_, lean_object* v_____do__lift_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2223_, v_____do__lift_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v_____do__lift_2224_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; lean_object* v_env_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2235_ = lean_st_ref_get(v___y_2233_);
v_env_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_ref(v_env_2236_);
lean_dec(v___x_2235_);
v___x_2237_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2236_, v_declName_2232_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2239_, v___y_2240_);
lean_dec(v___y_2240_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v_toApplicative_2251_; lean_object* v_toFunctor_2252_; lean_object* v_toSeq_2253_; lean_object* v_toSeqLeft_2254_; lean_object* v_toSeqRight_2255_; lean_object* v___f_2256_; lean_object* v___f_2257_; lean_object* v___f_2258_; lean_object* v___f_2259_; lean_object* v___x_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v_toApplicative_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2299_; 
v___x_2250_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2251_ = lean_ctor_get(v___x_2250_, 0);
v_toFunctor_2252_ = lean_ctor_get(v_toApplicative_2251_, 0);
v_toSeq_2253_ = lean_ctor_get(v_toApplicative_2251_, 2);
v_toSeqLeft_2254_ = lean_ctor_get(v_toApplicative_2251_, 3);
v_toSeqRight_2255_ = lean_ctor_get(v_toApplicative_2251_, 4);
v___f_2256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2257_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2252_, 2);
v___f_2258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2258_, 0, v_toFunctor_2252_);
v___f_2259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2259_, 0, v_toFunctor_2252_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___f_2258_);
lean_ctor_set(v___x_2260_, 1, v___f_2259_);
lean_inc(v_toSeqRight_2255_);
v___f_2261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2261_, 0, v_toSeqRight_2255_);
lean_inc(v_toSeqLeft_2254_);
v___f_2262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2262_, 0, v_toSeqLeft_2254_);
lean_inc(v_toSeq_2253_);
v___f_2263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2263_, 0, v_toSeq_2253_);
v___x_2264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2260_);
lean_ctor_set(v___x_2264_, 1, v___f_2256_);
lean_ctor_set(v___x_2264_, 2, v___f_2263_);
lean_ctor_set(v___x_2264_, 3, v___f_2262_);
lean_ctor_set(v___x_2264_, 4, v___f_2261_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___f_2257_);
v___x_2266_ = l_StateRefT_x27_instMonad___redArg(v___x_2265_);
v_toApplicative_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2299_ == 0)
{
lean_object* v_unused_2300_; 
v_unused_2300_ = lean_ctor_get(v___x_2266_, 1);
lean_dec(v_unused_2300_);
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2299_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_toApplicative_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2299_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v_toFunctor_2271_; lean_object* v_toSeq_2272_; lean_object* v_toSeqLeft_2273_; lean_object* v_toSeqRight_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2297_; 
v_toFunctor_2271_ = lean_ctor_get(v_toApplicative_2267_, 0);
v_toSeq_2272_ = lean_ctor_get(v_toApplicative_2267_, 2);
v_toSeqLeft_2273_ = lean_ctor_get(v_toApplicative_2267_, 3);
v_toSeqRight_2274_ = lean_ctor_get(v_toApplicative_2267_, 4);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_toApplicative_2267_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; 
v_unused_2298_ = lean_ctor_get(v_toApplicative_2267_, 1);
lean_dec(v_unused_2298_);
v___x_2276_ = v_toApplicative_2267_;
v_isShared_2277_ = v_isSharedCheck_2297_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_toSeqRight_2274_);
lean_inc(v_toSeqLeft_2273_);
lean_inc(v_toSeq_2272_);
lean_inc(v_toFunctor_2271_);
lean_dec(v_toApplicative_2267_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2297_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___f_2278_; lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___x_2287_; 
v___f_2278_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2271_);
v___f_2280_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2280_, 0, v_toFunctor_2271_);
v___f_2281_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2281_, 0, v_toFunctor_2271_);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___f_2280_);
lean_ctor_set(v___x_2282_, 1, v___f_2281_);
v___f_2283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2283_, 0, v_toSeqRight_2274_);
v___f_2284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2284_, 0, v_toSeqLeft_2273_);
v___f_2285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2285_, 0, v_toSeq_2272_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 4, v___f_2283_);
lean_ctor_set(v___x_2276_, 3, v___f_2284_);
lean_ctor_set(v___x_2276_, 2, v___f_2285_);
lean_ctor_set(v___x_2276_, 1, v___f_2278_);
lean_ctor_set(v___x_2276_, 0, v___x_2282_);
v___x_2287_ = v___x_2276_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___f_2278_);
lean_ctor_set(v_reuseFailAlloc_2296_, 2, v___f_2285_);
lean_ctor_set(v_reuseFailAlloc_2296_, 3, v___f_2284_);
lean_ctor_set(v_reuseFailAlloc_2296_, 4, v___f_2283_);
v___x_2287_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2289_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v___f_2279_);
lean_ctor_set(v___x_2269_, 0, v___x_2287_);
v___x_2289_ = v___x_2269_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___f_2279_);
v___x_2289_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_23469__overap_2293_; lean_object* v___x_2294_; 
v___x_2290_ = l_StateRefT_x27_instMonad___redArg(v___x_2289_);
v___x_2291_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2292_ = l_instInhabitedOfMonad___redArg(v___x_2290_, v___x_2291_);
v___x_23469__overap_2293_ = lean_panic_fn_borrowed(v___x_2292_, v_msg_2243_);
lean_dec(v___x_2292_);
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2245_);
lean_inc(v___y_2244_);
v___x_2294_ = lean_apply_6(v___x_23469__overap_2293_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, lean_box(0));
return v___x_2294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
return v_res_2308_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2309_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
lean_ctor_set(v___x_2314_, 2, v___x_2313_);
lean_ctor_set(v___x_2314_, 3, v___x_2313_);
lean_ctor_set(v___x_2314_, 4, v___x_2312_);
lean_ctor_set(v___x_2314_, 5, v___x_2312_);
lean_ctor_set(v___x_2314_, 6, v___x_2312_);
lean_ctor_set(v___x_2314_, 7, v___x_2312_);
lean_ctor_set(v___x_2314_, 8, v___x_2312_);
lean_ctor_set(v___x_2314_, 9, v___x_2312_);
lean_ctor_set(v___x_2314_, 10, v___x_2312_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_unsigned_to_nat(32u);
v___x_2316_ = lean_mk_empty_array_with_capacity(v___x_2315_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2318_ = ((size_t)5ULL);
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = lean_unsigned_to_nat(32u);
v___x_2321_ = lean_mk_empty_array_with_capacity(v___x_2320_);
v___x_2322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2323_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v___x_2321_);
lean_ctor_set(v___x_2323_, 2, v___x_2319_);
lean_ctor_set(v___x_2323_, 3, v___x_2319_);
lean_ctor_set_usize(v___x_2323_, 4, v___x_2318_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2324_ = lean_box(1);
v___x_2325_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
lean_ctor_set(v___x_2327_, 2, v___x_2324_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2333_ = l_Lean_stringToMessageData(v___x_2332_);
return v___x_2333_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2336_ = l_Lean_stringToMessageData(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2342_ = l_Lean_stringToMessageData(v___x_2341_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2345_ = l_Lean_stringToMessageData(v___x_2344_);
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2349_, lean_object* v_declHint_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v_env_2354_; uint8_t v___x_2355_; 
v___x_2353_ = lean_st_ref_get(v___y_2351_);
v_env_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc_ref(v_env_2354_);
lean_dec(v___x_2353_);
v___x_2355_ = l_Lean_Name_isAnonymous(v_declHint_2350_);
if (v___x_2355_ == 0)
{
uint8_t v_isExporting_2356_; 
v_isExporting_2356_ = lean_ctor_get_uint8(v_env_2354_, sizeof(void*)*8);
if (v_isExporting_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v_env_2354_);
lean_dec(v_declHint_2350_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_msg_2349_);
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
lean_inc_ref(v_env_2354_);
v___x_2358_ = l_Lean_Environment_setExporting(v_env_2354_, v___x_2355_);
lean_inc(v_declHint_2350_);
lean_inc_ref(v___x_2358_);
v___x_2359_ = l_Lean_Environment_contains(v___x_2358_, v_declHint_2350_, v_isExporting_2356_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
lean_dec_ref(v___x_2358_);
lean_dec_ref(v_env_2354_);
lean_dec(v_declHint_2350_);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v_msg_2349_);
return v___x_2360_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_c_2366_; lean_object* v___x_2367_; 
v___x_2361_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2362_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2363_ = l_Lean_Options_empty;
v___x_2364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2358_);
lean_ctor_set(v___x_2364_, 1, v___x_2361_);
lean_ctor_set(v___x_2364_, 2, v___x_2362_);
lean_ctor_set(v___x_2364_, 3, v___x_2363_);
lean_inc(v_declHint_2350_);
v___x_2365_ = l_Lean_MessageData_ofConstName(v_declHint_2350_, v___x_2355_);
v_c_2366_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2366_, 0, v___x_2364_);
lean_ctor_set(v_c_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2354_, v_declHint_2350_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v_env_2354_);
lean_dec(v_declHint_2350_);
v___x_2368_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
lean_ctor_set(v___x_2369_, 1, v_c_2366_);
v___x_2370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_MessageData_note(v___x_2371_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_msg_2349_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
else
{
lean_object* v_val_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2410_; 
v_val_2375_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2377_ = v___x_2367_;
v_isShared_2378_ = v_isSharedCheck_2410_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_val_2375_);
lean_dec(v___x_2367_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2410_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_mod_2382_; uint8_t v___x_2383_; 
v___x_2379_ = lean_box(0);
v___x_2380_ = l_Lean_Environment_header(v_env_2354_);
lean_dec_ref(v_env_2354_);
v___x_2381_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2380_);
v_mod_2382_ = lean_array_get(v___x_2379_, v___x_2381_, v_val_2375_);
lean_dec(v_val_2375_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = l_Lean_isPrivateName(v_declHint_2350_);
lean_dec(v_declHint_2350_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2384_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
lean_ctor_set(v___x_2385_, 1, v_c_2366_);
v___x_2386_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = l_Lean_MessageData_ofName(v_mod_2382_);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = l_Lean_MessageData_note(v___x_2391_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v_msg_2349_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set_tag(v___x_2377_, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2393_);
v___x_2395_ = v___x_2377_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2397_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v_c_2366_);
v___x_2399_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = l_Lean_MessageData_ofName(v_mod_2382_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = l_Lean_MessageData_note(v___x_2404_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_msg_2349_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set_tag(v___x_2377_, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2406_);
v___x_2408_ = v___x_2377_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2411_; 
lean_dec_ref(v_env_2354_);
lean_dec(v_declHint_2350_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v_msg_2349_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2412_, lean_object* v_declHint_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2412_, v_declHint_2413_, v___y_2414_);
lean_dec(v___y_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2417_, lean_object* v_declHint_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2435_; 
v___x_2425_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2417_, v_declHint_2418_, v___y_2423_);
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2430_ = l_Lean_unknownIdentifierMessageTag;
v___x_2431_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v_a_2426_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2431_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2436_, lean_object* v_declHint_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2436_, v_declHint_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_ref_2451_; lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2461_; 
v_ref_2451_ = lean_ctor_get(v___y_2448_, 2);
v___x_2452_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
lean_inc(v_ref_2451_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v_ref_2451_);
lean_ctor_set(v___x_2457_, 1, v_a_2453_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set_tag(v___x_2455_, 1);
lean_ctor_set(v___x_2455_, 0, v___x_2457_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2469_, lean_object* v_msg_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_toCold_2477_; lean_object* v_currRecDepth_2478_; lean_object* v_ref_2479_; uint8_t v_diag_2480_; uint8_t v_suppressElabErrors_2481_; lean_object* v_ref_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_toCold_2477_ = lean_ctor_get(v___y_2474_, 0);
v_currRecDepth_2478_ = lean_ctor_get(v___y_2474_, 1);
v_ref_2479_ = lean_ctor_get(v___y_2474_, 2);
v_diag_2480_ = lean_ctor_get_uint8(v___y_2474_, sizeof(void*)*3);
v_suppressElabErrors_2481_ = lean_ctor_get_uint8(v___y_2474_, sizeof(void*)*3 + 1);
v_ref_2482_ = l_Lean_replaceRef(v_ref_2469_, v_ref_2479_);
lean_inc(v_currRecDepth_2478_);
lean_inc_ref(v_toCold_2477_);
v___x_2483_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2483_, 0, v_toCold_2477_);
lean_ctor_set(v___x_2483_, 1, v_currRecDepth_2478_);
lean_ctor_set(v___x_2483_, 2, v_ref_2482_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*3, v_diag_2480_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*3 + 1, v_suppressElabErrors_2481_);
v___x_2484_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2470_, v___y_2472_, v___y_2473_, v___x_2483_, v___y_2475_);
lean_dec_ref_known(v___x_2483_, 3);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2485_, lean_object* v_msg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2485_, v_msg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec(v_ref_2485_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2494_, lean_object* v_msg_2495_, lean_object* v_declHint_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v_a_2504_; lean_object* v___x_2505_; 
v___x_2503_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2495_, v_declHint_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2494_, v_a_2504_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2506_, lean_object* v_msg_2507_, lean_object* v_declHint_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2506_, v_msg_2507_, v_declHint_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec(v_ref_2506_);
return v_res_2515_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2518_ = l_Lean_stringToMessageData(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2521_ = l_Lean_stringToMessageData(v___x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2522_, lean_object* v_constName_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2530_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2531_ = 0;
lean_inc(v_constName_2523_);
v___x_2532_ = l_Lean_MessageData_ofConstName(v_constName_2523_, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2530_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2522_, v___x_2535_, v_constName_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2537_, lean_object* v_constName_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2537_, v_constName_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec(v_ref_2537_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_ref_2553_; lean_object* v___x_2554_; 
v_ref_2553_ = lean_ctor_get(v___y_2550_, 2);
v___x_2554_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2553_, v_constName_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v_env_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2570_ = lean_st_ref_get(v___y_2568_);
v_env_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_ref(v_env_2571_);
lean_dec(v___x_2570_);
v___x_2572_ = 0;
lean_inc(v_constName_2563_);
v___x_2573_ = l_Lean_Environment_find_x3f(v_env_2571_, v_constName_2563_, v___x_2572_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
return v___x_2574_;
}
else
{
lean_object* v_val_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec(v_constName_2563_);
v_val_2575_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2573_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_val_2575_);
lean_dec(v___x_2573_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 0);
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_val_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
return v_res_2590_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2595_ = lean_unsigned_to_nat(53u);
v___x_2596_ = lean_unsigned_to_nat(62u);
v___x_2597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2599_ = l_mkPanicMessageWithDecl(v___x_2598_, v___x_2597_, v___x_2596_, v___x_2595_, v___x_2594_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2600_, size_t v_i_2601_, lean_object* v_bs_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_usize_dec_lt(v_i_2601_, v_sz_2600_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v_bs_2602_);
return v___x_2610_;
}
else
{
lean_object* v_v_2611_; lean_object* v___x_2612_; 
v_v_2611_ = lean_array_uget_borrowed(v_bs_2602_, v_i_2601_);
lean_inc(v_v_2611_);
v___x_2612_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2611_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; lean_object* v_bs_x27_2615_; lean_object* v_a_2617_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v___x_2614_ = lean_unsigned_to_nat(0u);
v_bs_x27_2615_ = lean_array_uset(v_bs_2602_, v_i_2601_, v___x_2614_);
if (lean_obj_tag(v_a_2613_) == 6)
{
lean_object* v_val_2622_; lean_object* v_numFields_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; 
v_val_2622_ = lean_ctor_get(v_a_2613_, 0);
lean_inc_ref(v_val_2622_);
lean_dec_ref_known(v_a_2613_, 1);
v_numFields_2623_ = lean_ctor_get(v_val_2622_, 4);
lean_inc(v_numFields_2623_);
lean_dec_ref(v_val_2622_);
v___x_2624_ = 0;
v___x_2625_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2625_, 0, v_numFields_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2614_);
lean_ctor_set_uint8(v___x_2625_, sizeof(void*)*2, v___x_2624_);
v_a_2617_ = v___x_2625_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec(v_a_2613_);
v___x_2626_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2627_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2626_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v_a_2617_ = v_a_2628_;
goto v___jp_2616_;
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref(v_bs_x27_2615_);
v_a_2629_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2627_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2627_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
v___jp_2616_:
{
size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((size_t)1ULL);
v___x_2619_ = lean_usize_add(v_i_2601_, v___x_2618_);
v___x_2620_ = lean_array_uset(v_bs_x27_2615_, v_i_2601_, v_a_2617_);
v_i_2601_ = v___x_2619_;
v_bs_2602_ = v___x_2620_;
goto _start;
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v_bs_2602_);
v_a_2637_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2612_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2612_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2645_, lean_object* v_i_2646_, lean_object* v_bs_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2645_);
lean_dec(v_sz_2645_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2646_);
lean_dec(v_i_2646_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2654_, v_i_boxed_2655_, v_bs_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
return v_res_2656_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_box(0);
v___x_2658_ = lean_unsigned_to_nat(16u);
v___x_2659_ = lean_mk_array(v___x_2658_, v___x_2657_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2661_ = lean_unsigned_to_nat(0u);
v___x_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v___x_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2665_, uint8_t v_alsoCasesOn_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = l_Lean_Expr_isApp(v_e_2665_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec_ref(v_e_2665_);
v___x_2677_ = lean_box(0);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Expr_getAppFn(v_e_2665_);
if (lean_obj_tag(v___x_2679_) == 4)
{
lean_object* v_declName_2680_; lean_object* v_us_2681_; lean_object* v___x_2682_; lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2836_; 
v_declName_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc_n(v_declName_2680_, 2);
v_us_2681_ = lean_ctor_get(v___x_2679_, 1);
lean_inc(v_us_2681_);
lean_dec_ref_known(v___x_2679_, 2);
v___x_2682_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2680_, v___y_2671_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2836_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2836_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_2683_) == 1)
{
lean_object* v_val_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2729_; 
v_val_2688_ = lean_ctor_get(v_a_2683_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_a_2683_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2690_ = v_a_2683_;
v_isShared_2691_ = v_isSharedCheck_2729_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_val_2688_);
lean_dec(v_a_2683_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2729_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_dummy_2692_; lean_object* v_nargs_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v_args_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v_dummy_2692_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2693_ = l_Lean_Expr_getAppNumArgs(v_e_2665_);
lean_inc(v_nargs_2693_);
v___x_2694_ = lean_mk_array(v_nargs_2693_, v_dummy_2692_);
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = lean_nat_sub(v_nargs_2693_, v___x_2695_);
lean_dec(v_nargs_2693_);
v_args_2697_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2665_, v___x_2694_, v___x_2696_);
v___x_2698_ = lean_array_get_size(v_args_2697_);
v___x_2699_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2688_);
v___x_2700_ = lean_nat_dec_lt(v___x_2698_, v___x_2699_);
lean_dec(v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v_numParams_2701_; lean_object* v_numDiscrs_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v_numParams_2701_ = lean_ctor_get(v_val_2688_, 0);
v_numDiscrs_2702_ = lean_ctor_get(v_val_2688_, 1);
v___x_2703_ = lean_array_mk(v_us_2681_);
v___x_2704_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2701_);
v___x_2705_ = l_Array_extract___redArg(v_args_2697_, v___x_2704_, v_numParams_2701_);
v___x_2706_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2688_);
v___x_2707_ = lean_array_get(v___x_2687_, v_args_2697_, v___x_2706_);
lean_dec(v___x_2706_);
v___x_2708_ = lean_nat_add(v_numParams_2701_, v___x_2695_);
v___x_2709_ = lean_nat_add(v___x_2708_, v_numDiscrs_2702_);
lean_inc(v___x_2709_);
lean_inc_ref_n(v_args_2697_, 2);
v___x_2710_ = l_Array_toSubarray___redArg(v_args_2697_, v___x_2708_, v___x_2709_);
v___x_2711_ = l_Subarray_copy___redArg(v___x_2710_);
v___x_2712_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2688_);
v___x_2713_ = lean_nat_add(v___x_2709_, v___x_2712_);
lean_dec(v___x_2712_);
lean_inc(v___x_2713_);
v___x_2714_ = l_Array_toSubarray___redArg(v_args_2697_, v___x_2709_, v___x_2713_);
v___x_2715_ = l_Subarray_copy___redArg(v___x_2714_);
v___x_2716_ = l_Array_toSubarray___redArg(v_args_2697_, v___x_2713_, v___x_2698_);
v___x_2717_ = l_Subarray_copy___redArg(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2718_, 0, v_val_2688_);
lean_ctor_set(v___x_2718_, 1, v_declName_2680_);
lean_ctor_set(v___x_2718_, 2, v___x_2703_);
lean_ctor_set(v___x_2718_, 3, v___x_2705_);
lean_ctor_set(v___x_2718_, 4, v___x_2707_);
lean_ctor_set(v___x_2718_, 5, v___x_2711_);
lean_ctor_set(v___x_2718_, 6, v___x_2715_);
lean_ctor_set(v___x_2718_, 7, v___x_2717_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2718_);
v___x_2720_ = v___x_2690_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2722_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2720_);
v___x_2722_ = v___x_2685_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_dec_ref(v_args_2697_);
lean_del_object(v___x_2690_);
lean_dec(v_val_2688_);
lean_dec(v_us_2681_);
lean_dec(v_declName_2680_);
v___x_2725_ = lean_box(0);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2725_);
v___x_2727_ = v___x_2685_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v___x_2730_; 
lean_del_object(v___x_2685_);
lean_dec(v_a_2683_);
v___x_2730_ = lean_st_ref_get(v___y_2671_);
if (v_alsoCasesOn_2666_ == 0)
{
lean_dec(v___x_2730_);
lean_dec(v_us_2681_);
lean_dec(v_declName_2680_);
lean_dec_ref(v_e_2665_);
goto v___jp_2673_;
}
else
{
lean_object* v_env_2731_; uint8_t v___x_2732_; 
v_env_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc_ref(v_env_2731_);
lean_dec(v___x_2730_);
lean_inc(v_declName_2680_);
v___x_2732_ = l_Lean_isCasesOnRecursor(v_env_2731_, v_declName_2680_);
if (v___x_2732_ == 0)
{
lean_dec(v_us_2681_);
lean_dec(v_declName_2680_);
lean_dec_ref(v_e_2665_);
goto v___jp_2673_;
}
else
{
lean_object* v_indName_2733_; lean_object* v___x_2734_; 
v_indName_2733_ = l_Lean_Name_getPrefix(v_declName_2680_);
v___x_2734_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2733_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2827_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2827_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2827_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
if (lean_obj_tag(v_a_2735_) == 5)
{
lean_object* v_val_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2822_; 
v_val_2739_ = lean_ctor_get(v_a_2735_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_a_2735_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2741_ = v_a_2735_;
v_isShared_2742_ = v_isSharedCheck_2822_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_val_2739_);
lean_dec(v_a_2735_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2822_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_toConstantVal_2743_; lean_object* v_numParams_2744_; lean_object* v_numIndices_2745_; lean_object* v_ctors_2746_; lean_object* v_nargs_2747_; lean_object* v_dummy_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v_args_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v_toConstantVal_2743_ = lean_ctor_get(v_val_2739_, 0);
lean_inc_ref(v_toConstantVal_2743_);
v_numParams_2744_ = lean_ctor_get(v_val_2739_, 1);
lean_inc(v_numParams_2744_);
v_numIndices_2745_ = lean_ctor_get(v_val_2739_, 2);
lean_inc(v_numIndices_2745_);
v_ctors_2746_ = lean_ctor_get(v_val_2739_, 4);
lean_inc(v_ctors_2746_);
v_nargs_2747_ = l_Lean_Expr_getAppNumArgs(v_e_2665_);
v_dummy_2748_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2747_);
v___x_2749_ = lean_mk_array(v_nargs_2747_, v_dummy_2748_);
v___x_2750_ = lean_unsigned_to_nat(1u);
v___x_2751_ = lean_nat_sub(v_nargs_2747_, v___x_2750_);
lean_dec(v_nargs_2747_);
v_args_2752_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2665_, v___x_2749_, v___x_2751_);
v___x_2753_ = lean_nat_add(v_numParams_2744_, v___x_2750_);
v___x_2754_ = lean_nat_add(v___x_2753_, v_numIndices_2745_);
v___x_2755_ = lean_nat_add(v___x_2754_, v___x_2750_);
lean_dec(v___x_2754_);
v___x_2756_ = l_Lean_InductiveVal_numCtors(v_val_2739_);
lean_dec_ref(v_val_2739_);
v___x_2757_ = lean_nat_add(v___x_2755_, v___x_2756_);
lean_dec(v___x_2756_);
v___x_2758_ = lean_array_get_size(v_args_2752_);
v___x_2759_ = lean_nat_dec_le(v___x_2757_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2762_; 
lean_dec(v___x_2757_);
lean_dec(v___x_2755_);
lean_dec(v___x_2753_);
lean_dec_ref(v_args_2752_);
lean_dec(v_ctors_2746_);
lean_dec(v_numIndices_2745_);
lean_dec(v_numParams_2744_);
lean_dec_ref(v_toConstantVal_2743_);
lean_del_object(v___x_2741_);
lean_dec(v_us_2681_);
lean_dec(v_declName_2680_);
v___x_2760_ = lean_box(0);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2760_);
v___x_2762_ = v___x_2737_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
else
{
lean_object* v___x_2764_; lean_object* v_params_2765_; lean_object* v_motive_2766_; lean_object* v_discrs_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v_discrInfos_2770_; lean_object* v_alts_2771_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v_lower_2813_; lean_object* v_upper_2814_; uint8_t v___x_2821_; 
lean_del_object(v___x_2737_);
v___x_2764_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2744_);
lean_inc_ref_n(v_args_2752_, 3);
v_params_2765_ = l_Array_toSubarray___redArg(v_args_2752_, v___x_2764_, v_numParams_2744_);
v_motive_2766_ = lean_array_get(v___x_2687_, v_args_2752_, v_numParams_2744_);
lean_dec(v_numParams_2744_);
lean_inc(v___x_2755_);
v_discrs_2767_ = l_Array_toSubarray___redArg(v_args_2752_, v___x_2753_, v___x_2755_);
v___x_2768_ = lean_nat_add(v_numIndices_2745_, v___x_2750_);
lean_dec(v_numIndices_2745_);
v___x_2769_ = lean_box(0);
v_discrInfos_2770_ = lean_mk_array(v___x_2768_, v___x_2769_);
lean_inc(v___x_2757_);
v_alts_2771_ = l_Array_toSubarray___redArg(v_args_2752_, v___x_2755_, v___x_2757_);
v___x_2821_ = lean_nat_dec_le(v___x_2757_, v___x_2764_);
if (v___x_2821_ == 0)
{
v_lower_2813_ = v___x_2757_;
v_upper_2814_ = v___x_2758_;
goto v___jp_2812_;
}
else
{
lean_dec(v___x_2757_);
v_lower_2813_ = v___x_2764_;
v_upper_2814_ = v___x_2758_;
goto v___jp_2812_;
}
v___jp_2772_:
{
lean_object* v___x_2775_; size_t v_sz_2776_; size_t v___x_2777_; lean_object* v___x_2778_; 
v___x_2775_ = lean_array_mk(v_ctors_2746_);
v_sz_2776_ = lean_array_size(v___x_2775_);
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2776_, v___x_2777_, v___x_2775_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2803_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2803_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2803_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_start_2783_; lean_object* v_stop_2784_; lean_object* v_start_2785_; lean_object* v_stop_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v_start_2783_ = lean_ctor_get(v_params_2765_, 1);
lean_inc(v_start_2783_);
v_stop_2784_ = lean_ctor_get(v_params_2765_, 2);
lean_inc(v_stop_2784_);
v_start_2785_ = lean_ctor_get(v_discrs_2767_, 1);
lean_inc(v_start_2785_);
v_stop_2786_ = lean_ctor_get(v_discrs_2767_, 2);
lean_inc(v_stop_2786_);
v___x_2787_ = lean_nat_sub(v_stop_2784_, v_start_2783_);
lean_dec(v_start_2783_);
lean_dec(v_stop_2784_);
v___x_2788_ = lean_nat_sub(v_stop_2786_, v_start_2785_);
lean_dec(v_start_2785_);
lean_dec(v_stop_2786_);
v___x_2789_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2787_);
lean_ctor_set(v___x_2790_, 1, v___x_2788_);
lean_ctor_set(v___x_2790_, 2, v_a_2779_);
lean_ctor_set(v___x_2790_, 3, v___y_2774_);
lean_ctor_set(v___x_2790_, 4, v_discrInfos_2770_);
lean_ctor_set(v___x_2790_, 5, v___x_2789_);
v___x_2791_ = lean_array_mk(v_us_2681_);
v___x_2792_ = l_Subarray_copy___redArg(v_params_2765_);
v___x_2793_ = l_Subarray_copy___redArg(v_discrs_2767_);
v___x_2794_ = l_Subarray_copy___redArg(v_alts_2771_);
v___x_2795_ = l_Subarray_copy___redArg(v___y_2773_);
v___x_2796_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2790_);
lean_ctor_set(v___x_2796_, 1, v_declName_2680_);
lean_ctor_set(v___x_2796_, 2, v___x_2791_);
lean_ctor_set(v___x_2796_, 3, v___x_2792_);
lean_ctor_set(v___x_2796_, 4, v_motive_2766_);
lean_ctor_set(v___x_2796_, 5, v___x_2793_);
lean_ctor_set(v___x_2796_, 6, v___x_2794_);
lean_ctor_set(v___x_2796_, 7, v___x_2795_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set_tag(v___x_2741_, 1);
lean_ctor_set(v___x_2741_, 0, v___x_2796_);
v___x_2798_ = v___x_2741_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2800_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2798_);
v___x_2800_ = v___x_2781_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v_alts_2771_);
lean_dec_ref(v_discrInfos_2770_);
lean_dec_ref(v_discrs_2767_);
lean_dec(v_motive_2766_);
lean_dec_ref(v_params_2765_);
lean_del_object(v___x_2741_);
lean_dec(v_us_2681_);
lean_dec(v_declName_2680_);
v_a_2804_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2778_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2778_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
v___jp_2812_:
{
lean_object* v_levelParams_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v_levelParams_2815_ = lean_ctor_get(v_toConstantVal_2743_, 1);
lean_inc(v_levelParams_2815_);
lean_dec_ref(v_toConstantVal_2743_);
v___x_2816_ = l_Array_toSubarray___redArg(v_args_2752_, v_lower_2813_, v_upper_2814_);
v___x_2817_ = l_List_lengthTR___redArg(v_levelParams_2815_);
lean_dec(v_levelParams_2815_);
v___x_2818_ = l_List_lengthTR___redArg(v_us_2681_);
v___x_2819_ = lean_nat_dec_eq(v___x_2817_, v___x_2818_);
lean_dec(v___x_2818_);
lean_dec(v___x_2817_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
v___x_2820_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2773_ = v___x_2816_;
v___y_2774_ = v___x_2820_;
goto v___jp_2772_;
}
else
{
v___y_2773_ = v___x_2816_;
v___y_2774_ = v___x_2769_;
goto v___jp_2772_;
}
}
}
}
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
lean_dec(v_a_2735_);
lean_dec(v_us_2681_);
lean_dec(v_declName_2680_);
lean_dec_ref(v_e_2665_);
v___x_2823_ = lean_box(0);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2823_);
v___x_2825_ = v___x_2737_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_us_2681_);
lean_dec(v_declName_2680_);
lean_dec_ref(v_e_2665_);
v_a_2828_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2734_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2734_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
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
lean_dec_ref(v___x_2679_);
lean_dec_ref(v_e_2665_);
goto v___jp_2673_;
}
}
v___jp_2673_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2837_, lean_object* v_alsoCasesOn_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2845_; lean_object* v_res_2846_; 
v_alsoCasesOn_boxed_2845_ = lean_unbox(v_alsoCasesOn_2838_);
v_res_2846_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2837_, v_alsoCasesOn_boxed_2845_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
if (lean_obj_tag(v_a_2847_) == 0)
{
lean_object* v___x_2849_; 
v___x_2849_ = l_List_reverse___redArg(v_a_2848_);
return v___x_2849_;
}
else
{
lean_object* v_head_2850_; lean_object* v_tail_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2860_; 
v_head_2850_ = lean_ctor_get(v_a_2847_, 0);
v_tail_2851_ = lean_ctor_get(v_a_2847_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_a_2847_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2853_ = v_a_2847_;
v_isShared_2854_ = v_isSharedCheck_2860_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_tail_2851_);
lean_inc(v_head_2850_);
lean_dec(v_a_2847_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2860_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = l_Lean_MessageData_ofExpr(v_head_2850_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v_a_2848_);
lean_ctor_set(v___x_2853_, 0, v___x_2855_);
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_a_2848_);
v___x_2857_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
v_a_2847_ = v_tail_2851_;
v_a_2848_ = v___x_2857_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2861_, lean_object* v_x_2862_){
_start:
{
lean_object* v_fnName_2863_; uint8_t v___x_2864_; 
v_fnName_2863_ = lean_ctor_get(v_x_2862_, 0);
v___x_2864_ = l_Lean_Expr_isConstOf(v_x_2861_, v_fnName_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_res_2867_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2865_, v_x_2866_);
lean_dec_ref(v_x_2866_);
lean_dec_ref(v_x_2865_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2869_, lean_object* v_type_2870_, lean_object* v_val_2871_, lean_object* v_k_2872_, uint8_t v_nondep_2873_, uint8_t v_kind_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___f_2881_; lean_object* v___x_2882_; 
lean_inc(v___y_2875_);
v___f_2881_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2881_, 0, v_k_2872_);
lean_closure_set(v___f_2881_, 1, v___y_2875_);
v___x_2882_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2869_, v_type_2870_, v_val_2871_, v___f_2881_, v_nondep_2873_, v_kind_2874_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2882_) == 0)
{
return v___x_2882_;
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2882_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2891_, lean_object* v_type_2892_, lean_object* v_val_2893_, lean_object* v_k_2894_, lean_object* v_nondep_2895_, lean_object* v_kind_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
uint8_t v_nondep_boxed_2903_; uint8_t v_kind_boxed_2904_; lean_object* v_res_2905_; 
v_nondep_boxed_2903_ = lean_unbox(v_nondep_2895_);
v_kind_boxed_2904_ = lean_unbox(v_kind_2896_);
v_res_2905_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2891_, v_type_2892_, v_val_2893_, v_k_2894_, v_nondep_boxed_2903_, v_kind_boxed_2904_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2906_, uint8_t v_usedLetOnly_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2912_);
lean_inc(v___y_2911_);
lean_inc_ref(v___y_2910_);
lean_inc(v___y_2909_);
lean_inc_ref(v_x_2908_);
v___x_2915_ = lean_apply_7(v_k_2906_, v_x_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, lean_box(0));
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = lean_unsigned_to_nat(1u);
v___x_2918_ = lean_mk_empty_array_with_capacity(v___x_2917_);
v___x_2919_ = lean_array_push(v___x_2918_, v_x_2908_);
v___x_2920_ = 0;
v___x_2921_ = 1;
v___x_2922_ = l_Lean_Meta_mkLetFVars(v___x_2919_, v_a_2916_, v_usedLetOnly_2907_, v___x_2920_, v___x_2921_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec_ref(v___x_2919_);
return v___x_2922_;
}
else
{
lean_dec_ref(v_x_2908_);
return v___x_2915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2923_, lean_object* v_usedLetOnly_2924_, lean_object* v_x_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
uint8_t v_usedLetOnly_boxed_2932_; lean_object* v_res_2933_; 
v_usedLetOnly_boxed_2932_ = lean_unbox(v_usedLetOnly_2924_);
v_res_2933_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2923_, v_usedLetOnly_boxed_2932_, v_x_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2934_, lean_object* v_type_2935_, lean_object* v_val_2936_, lean_object* v_k_2937_, uint8_t v_nondep_2938_, uint8_t v_kind_2939_, uint8_t v_usedLetOnly_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___x_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_box(v_usedLetOnly_2940_);
v___f_2948_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2948_, 0, v_k_2937_);
lean_closure_set(v___f_2948_, 1, v___x_2947_);
v___x_2949_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2934_, v_type_2935_, v_val_2936_, v___f_2948_, v_nondep_2938_, v_kind_2939_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2950_, lean_object* v_type_2951_, lean_object* v_val_2952_, lean_object* v_k_2953_, lean_object* v_nondep_2954_, lean_object* v_kind_2955_, lean_object* v_usedLetOnly_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
uint8_t v_nondep_boxed_2963_; uint8_t v_kind_boxed_2964_; uint8_t v_usedLetOnly_boxed_2965_; lean_object* v_res_2966_; 
v_nondep_boxed_2963_ = lean_unbox(v_nondep_2954_);
v_kind_boxed_2964_ = lean_unbox(v_kind_2955_);
v_usedLetOnly_boxed_2965_ = lean_unbox(v_usedLetOnly_2956_);
v_res_2966_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2950_, v_type_2951_, v_val_2952_, v_k_2953_, v_nondep_boxed_2963_, v_kind_boxed_2964_, v_usedLetOnly_boxed_2965_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_2967_, lean_object* v_positions_2968_, lean_object* v_recFnNames_2969_, lean_object* v_containsRecFn_2970_, lean_object* v_below_2971_, size_t v_sz_2972_, size_t v_i_2973_, lean_object* v_bs_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
uint8_t v___x_2981_; 
v___x_2981_ = lean_usize_dec_lt(v_i_2973_, v_sz_2972_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_dec_ref(v_below_2971_);
lean_dec_ref(v_containsRecFn_2970_);
lean_dec_ref(v_recFnNames_2969_);
lean_dec_ref(v_positions_2968_);
lean_dec_ref(v_recArgInfos_2967_);
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_bs_2974_);
return v___x_2982_;
}
else
{
lean_object* v_v_2983_; lean_object* v___x_2984_; 
v_v_2983_ = lean_array_uget_borrowed(v_bs_2974_, v_i_2973_);
lean_inc_ref(v___y_2978_);
lean_inc(v_v_2983_);
lean_inc_ref(v_below_2971_);
lean_inc_ref(v_containsRecFn_2970_);
lean_inc_ref(v_recFnNames_2969_);
lean_inc_ref(v_positions_2968_);
lean_inc_ref(v_recArgInfos_2967_);
v___x_2984_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_2967_, v_positions_2968_, v_recFnNames_2969_, v_containsRecFn_2970_, v_below_2971_, v_v_2983_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2986_; lean_object* v_bs_x27_2987_; size_t v___x_2988_; size_t v___x_2989_; lean_object* v___x_2990_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2984_, 1);
v___x_2986_ = lean_unsigned_to_nat(0u);
v_bs_x27_2987_ = lean_array_uset(v_bs_2974_, v_i_2973_, v___x_2986_);
v___x_2988_ = ((size_t)1ULL);
v___x_2989_ = lean_usize_add(v_i_2973_, v___x_2988_);
v___x_2990_ = lean_array_uset(v_bs_x27_2987_, v_i_2973_, v_a_2985_);
v_i_2973_ = v___x_2989_;
v_bs_2974_ = v___x_2990_;
goto _start;
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v_bs_2974_);
lean_dec_ref(v_below_2971_);
lean_dec_ref(v_containsRecFn_2970_);
lean_dec_ref(v_recFnNames_2969_);
lean_dec_ref(v_positions_2968_);
lean_dec_ref(v_recArgInfos_2967_);
v_a_2992_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2984_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2984_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3002_ = l_Lean_stringToMessageData(v___x_3001_);
return v___x_3002_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3005_ = l_Lean_stringToMessageData(v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3006_, lean_object* v_positions_3007_, lean_object* v_recFnNames_3008_, lean_object* v_containsRecFn_3009_, lean_object* v_below_3010_, lean_object* v_e_3011_, lean_object* v_x_3012_, lean_object* v_x_3013_, lean_object* v_x_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
if (lean_obj_tag(v_x_3012_) == 5)
{
lean_object* v_fn_3021_; lean_object* v_arg_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_fn_3021_ = lean_ctor_get(v_x_3012_, 0);
lean_inc_ref(v_fn_3021_);
v_arg_3022_ = lean_ctor_get(v_x_3012_, 1);
lean_inc_ref(v_arg_3022_);
lean_dec_ref_known(v_x_3012_, 2);
v___x_3023_ = lean_array_set(v_x_3013_, v_x_3014_, v_arg_3022_);
v___x_3024_ = lean_unsigned_to_nat(1u);
v___x_3025_ = lean_nat_sub(v_x_3014_, v___x_3024_);
lean_dec(v_x_3014_);
v_x_3012_ = v_fn_3021_;
v_x_3013_ = v___x_3023_;
v_x_3014_ = v___x_3025_;
goto _start;
}
else
{
lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_dec(v_x_3014_);
lean_inc_ref(v_x_3012_);
v___f_3027_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3027_, 0, v_x_3012_);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3027_, v_recArgInfos_3006_, v___x_3028_);
if (lean_obj_tag(v___x_3029_) == 1)
{
lean_object* v_val_3030_; lean_object* v___x_3031_; lean_object* v___y_3033_; lean_object* v_recArgPos_3059_; lean_object* v_indGroupInst_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
lean_dec_ref(v_x_3012_);
v_val_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_val_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = lean_array_fget_borrowed(v_recArgInfos_3006_, v_val_3030_);
v_recArgPos_3059_ = lean_ctor_get(v___x_3031_, 2);
v_indGroupInst_3060_ = lean_ctor_get(v___x_3031_, 4);
v___x_3061_ = lean_array_get_size(v_x_3013_);
v___x_3062_ = lean_nat_dec_lt(v_recArgPos_3059_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_dec(v_val_3030_);
lean_dec_ref(v_x_3013_);
lean_dec_ref(v_below_3010_);
lean_dec_ref(v_containsRecFn_3009_);
lean_dec_ref(v_recFnNames_3008_);
lean_dec_ref(v_positions_3007_);
lean_dec_ref(v_recArgInfos_3006_);
v___x_3063_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3064_ = l_Lean_indentExpr(v_e_3011_);
v___x_3065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3065_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_array_fget_borrowed(v_x_3013_, v_recArgPos_3059_);
lean_inc_ref(v___y_3018_);
lean_inc(v___x_3067_);
lean_inc_ref(v_below_3010_);
lean_inc_ref(v_containsRecFn_3009_);
lean_inc_ref(v_recFnNames_3008_);
lean_inc_ref(v_positions_3007_);
lean_inc_ref(v_recArgInfos_3006_);
v___x_3068_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3006_, v_positions_3007_, v_recFnNames_3008_, v_containsRecFn_3009_, v_below_3010_, v___x_3067_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v_params_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v_params_3070_ = lean_ctor_get(v_indGroupInst_3060_, 2);
v___x_3071_ = lean_array_get_size(v_params_3070_);
lean_inc_ref(v_positions_3007_);
lean_inc_ref(v_below_3010_);
v___x_3072_ = l_Lean_Elab_Structural_toBelow(v_below_3010_, v___x_3071_, v_positions_3007_, v_val_3030_, v_a_3069_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_dec_ref(v_e_3011_);
v___y_3033_ = v___x_3072_;
goto v___jp_3032_;
}
else
{
lean_object* v_a_3073_; uint8_t v___y_3075_; uint8_t v___x_3080_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
v___x_3080_ = l_Lean_Exception_isInterrupt(v_a_3073_);
if (v___x_3080_ == 0)
{
uint8_t v___x_3081_; 
v___x_3081_ = l_Lean_Exception_isRuntime(v_a_3073_);
v___y_3075_ = v___x_3081_;
goto v___jp_3074_;
}
else
{
lean_dec(v_a_3073_);
v___y_3075_ = v___x_3080_;
goto v___jp_3074_;
}
v___jp_3074_:
{
if (v___y_3075_ == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec_ref_known(v___x_3072_, 1);
v___x_3076_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3077_ = l_Lean_indentExpr(v_e_3011_);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3078_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
v___y_3033_ = v___x_3079_;
goto v___jp_3032_;
}
else
{
lean_dec_ref(v_e_3011_);
v___y_3033_ = v___x_3072_;
goto v___jp_3032_;
}
}
}
}
else
{
lean_dec(v_val_3030_);
lean_dec_ref(v_x_3013_);
lean_dec_ref(v_e_3011_);
lean_dec_ref(v_below_3010_);
lean_dec_ref(v_containsRecFn_3009_);
lean_dec_ref(v_recFnNames_3008_);
lean_dec_ref(v_positions_3007_);
lean_dec_ref(v_recArgInfos_3006_);
return v___x_3068_;
}
}
v___jp_3032_:
{
if (lean_obj_tag(v___y_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v_fixedParamPerm_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_snd_3038_; size_t v_sz_3039_; size_t v___x_3040_; lean_object* v___x_3041_; 
v_a_3034_ = lean_ctor_get(v___y_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___y_3033_, 1);
v_fixedParamPerm_3035_ = lean_ctor_get(v___x_3031_, 1);
v___x_3036_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3035_, v_x_3013_);
lean_dec_ref(v_x_3013_);
lean_inc(v___x_3031_);
v___x_3037_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3031_, v___x_3036_);
v_snd_3038_ = lean_ctor_get(v___x_3037_, 1);
lean_inc(v_snd_3038_);
lean_dec_ref(v___x_3037_);
v_sz_3039_ = lean_array_size(v_snd_3038_);
v___x_3040_ = ((size_t)0ULL);
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3006_, v_positions_3007_, v_recFnNames_3008_, v_containsRecFn_3009_, v_below_3010_, v_sz_3039_, v___x_3040_, v_snd_3038_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3050_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3050_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3050_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3046_ = l_Lean_mkAppN(v_a_3034_, v_a_3042_);
lean_dec(v_a_3042_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___x_3046_);
v___x_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec(v_a_3034_);
v_a_3051_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3041_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3041_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_dec_ref(v_x_3013_);
lean_dec_ref(v_below_3010_);
lean_dec_ref(v_containsRecFn_3009_);
lean_dec_ref(v_recFnNames_3008_);
lean_dec_ref(v_positions_3007_);
lean_dec_ref(v_recArgInfos_3006_);
return v___y_3033_;
}
}
}
else
{
lean_object* v___x_3082_; 
lean_dec(v___x_3029_);
lean_dec_ref(v_e_3011_);
lean_inc_ref(v___y_3018_);
lean_inc_ref(v_below_3010_);
lean_inc_ref(v_containsRecFn_3009_);
lean_inc_ref(v_recFnNames_3008_);
lean_inc_ref(v_positions_3007_);
lean_inc_ref(v_recArgInfos_3006_);
v___x_3082_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3006_, v_positions_3007_, v_recFnNames_3008_, v_containsRecFn_3009_, v_below_3010_, v_x_3012_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; size_t v_sz_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v_sz_3084_ = lean_array_size(v_x_3013_);
v___x_3085_ = ((size_t)0ULL);
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3006_, v_positions_3007_, v_recFnNames_3008_, v_containsRecFn_3009_, v_below_3010_, v_sz_3084_, v___x_3085_, v_x_3013_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3095_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3095_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3095_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3091_ = l_Lean_mkAppN(v_a_3083_, v_a_3087_);
lean_dec(v_a_3087_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3093_ = v___x_3089_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3083_);
v_a_3096_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3086_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3086_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_dec_ref(v_x_3013_);
lean_dec_ref(v_below_3010_);
lean_dec_ref(v_containsRecFn_3009_);
lean_dec_ref(v_recFnNames_3008_);
lean_dec_ref(v_positions_3007_);
lean_dec_ref(v_recArgInfos_3006_);
return v___x_3082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3104_, lean_object* v_recArgInfos_3105_, lean_object* v_positions_3106_, lean_object* v_recFnNames_3107_, lean_object* v_containsRecFn_3108_, lean_object* v_below_3109_, uint8_t v___x_3110_, uint8_t v_a_3111_, lean_object* v_x_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_expr_instantiate1(v_body_3104_, v_x_3112_);
lean_inc_ref(v___y_3116_);
v___x_3120_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3105_, v_positions_3106_, v_recFnNames_3107_, v_containsRecFn_3108_, v_below_3109_, v___x_3119_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = lean_unsigned_to_nat(1u);
v___x_3123_ = lean_mk_empty_array_with_capacity(v___x_3122_);
v___x_3124_ = lean_array_push(v___x_3123_, v_x_3112_);
v___x_3125_ = 1;
v___x_3126_ = l_Lean_Meta_mkLambdaFVars(v___x_3124_, v_a_3121_, v___x_3110_, v_a_3111_, v___x_3110_, v_a_3111_, v___x_3125_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec_ref(v___x_3124_);
return v___x_3126_;
}
else
{
lean_dec_ref(v_x_3112_);
return v___x_3120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3127_, lean_object* v_recArgInfos_3128_, lean_object* v_positions_3129_, lean_object* v_recFnNames_3130_, lean_object* v_containsRecFn_3131_, lean_object* v_below_3132_, lean_object* v___x_3133_, lean_object* v_a_3134_, lean_object* v_x_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v___x_28443__boxed_3142_; uint8_t v_a_28444__boxed_3143_; lean_object* v_res_3144_; 
v___x_28443__boxed_3142_ = lean_unbox(v___x_3133_);
v_a_28444__boxed_3143_ = lean_unbox(v_a_3134_);
v_res_3144_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3127_, v_recArgInfos_3128_, v_positions_3129_, v_recFnNames_3130_, v_containsRecFn_3131_, v_below_3132_, v___x_28443__boxed_3142_, v_a_28444__boxed_3143_, v_x_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v_body_3127_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3145_, lean_object* v_recArgInfos_3146_, lean_object* v_positions_3147_, lean_object* v_recFnNames_3148_, lean_object* v_containsRecFn_3149_, lean_object* v_below_3150_, uint8_t v___x_3151_, uint8_t v_a_3152_, lean_object* v_x_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_expr_instantiate1(v_body_3145_, v_x_3153_);
lean_inc_ref(v___y_3157_);
v___x_3161_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3146_, v_positions_3147_, v_recFnNames_3148_, v_containsRecFn_3149_, v_below_3150_, v___x_3160_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; lean_object* v___x_3167_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = lean_unsigned_to_nat(1u);
v___x_3164_ = lean_mk_empty_array_with_capacity(v___x_3163_);
v___x_3165_ = lean_array_push(v___x_3164_, v_x_3153_);
v___x_3166_ = 1;
v___x_3167_ = l_Lean_Meta_mkForallFVars(v___x_3165_, v_a_3162_, v___x_3151_, v_a_3152_, v_a_3152_, v___x_3166_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec_ref(v___x_3165_);
return v___x_3167_;
}
else
{
lean_dec_ref(v_x_3153_);
return v___x_3161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3168_, lean_object* v_recArgInfos_3169_, lean_object* v_positions_3170_, lean_object* v_recFnNames_3171_, lean_object* v_containsRecFn_3172_, lean_object* v_below_3173_, lean_object* v___x_3174_, lean_object* v_a_3175_, lean_object* v_x_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
uint8_t v___x_28461__boxed_3183_; uint8_t v_a_28462__boxed_3184_; lean_object* v_res_3185_; 
v___x_28461__boxed_3183_ = lean_unbox(v___x_3174_);
v_a_28462__boxed_3184_ = lean_unbox(v_a_3175_);
v_res_3185_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3168_, v_recArgInfos_3169_, v_positions_3170_, v_recFnNames_3171_, v_containsRecFn_3172_, v_below_3173_, v___x_28461__boxed_3183_, v_a_28462__boxed_3184_, v_x_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v_body_3168_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3186_, lean_object* v_recArgInfos_3187_, lean_object* v_positions_3188_, lean_object* v_recFnNames_3189_, lean_object* v_containsRecFn_3190_, lean_object* v_below_3191_, lean_object* v_x_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3186_, v_recArgInfos_3187_, v_positions_3188_, v_recFnNames_3189_, v_containsRecFn_3190_, v_below_3191_, v_x_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v_x_3192_);
lean_dec_ref(v_body_3186_);
return v_res_3199_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3204_ = l_Lean_stringToMessageData(v___x_3203_);
return v___x_3204_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3207_ = l_Lean_stringToMessageData(v___x_3206_);
return v___x_3207_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3210_ = l_Lean_stringToMessageData(v___x_3209_);
return v___x_3210_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3213_ = l_Lean_stringToMessageData(v___x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v___x_3214_, lean_object* v_b_3215_, lean_object* v_recArgInfos_3216_, lean_object* v_positions_3217_, lean_object* v_recFnNames_3218_, lean_object* v_containsRecFn_3219_, uint8_t v___x_3220_, uint8_t v_a_3221_, lean_object* v___x_3222_, lean_object* v_a_3223_, lean_object* v_e_3224_, lean_object* v___x_3225_, lean_object* v_xs_3226_, lean_object* v_altBody_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v_toCold_3269_; lean_object* v_options_3270_; uint8_t v_hasTrace_3271_; 
v_toCold_3269_ = lean_ctor_get(v___y_3231_, 0);
v_options_3270_ = lean_ctor_get(v_toCold_3269_, 2);
v_hasTrace_3271_ = lean_ctor_get_uint8(v_options_3270_, sizeof(void*)*1);
if (v_hasTrace_3271_ == 0)
{
lean_dec(v___x_3225_);
v___y_3246_ = v___y_3228_;
v___y_3247_ = v___y_3229_;
v___y_3248_ = v___y_3230_;
v___y_3249_ = v___y_3231_;
v___y_3250_ = v___y_3232_;
goto v___jp_3245_;
}
else
{
lean_object* v_inheritedTraceOptions_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; 
v_inheritedTraceOptions_3272_ = lean_ctor_get(v_toCold_3269_, 11);
v___x_3273_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3225_);
v___x_3274_ = l_Lean_Name_append(v___x_3273_, v___x_3225_);
v___x_3275_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3272_, v_options_3270_, v___x_3274_);
lean_dec(v___x_3274_);
if (v___x_3275_ == 0)
{
lean_dec(v___x_3225_);
v___y_3246_ = v___y_3228_;
v___y_3247_ = v___y_3229_;
v___y_3248_ = v___y_3230_;
v___y_3249_ = v___y_3231_;
v___y_3250_ = v___y_3232_;
goto v___jp_3245_;
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3276_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3215_);
v___x_3277_ = l_Nat_reprFast(v_b_3215_);
v___x_3278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
v___x_3279_ = l_Lean_MessageData_ofFormat(v___x_3278_);
v___x_3280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3276_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
lean_inc_ref(v_xs_3226_);
v___x_3283_ = lean_array_to_list(v_xs_3226_);
v___x_3284_ = lean_box(0);
v___x_3285_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3283_, v___x_3284_);
v___x_3286_ = l_Lean_MessageData_ofList(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3282_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3225_, v___x_3287_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_dec_ref_known(v___x_3288_, 1);
v___y_3246_ = v___y_3228_;
v___y_3247_ = v___y_3229_;
v___y_3248_ = v___y_3230_;
v___y_3249_ = v___y_3231_;
v___y_3250_ = v___y_3232_;
goto v___jp_3245_;
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref(v_altBody_3227_);
lean_dec_ref(v_xs_3226_);
lean_dec_ref(v_e_3224_);
lean_dec_ref(v_a_3223_);
lean_dec_ref(v_containsRecFn_3219_);
lean_dec_ref(v_recFnNames_3218_);
lean_dec_ref(v_positions_3217_);
lean_dec_ref(v_recArgInfos_3216_);
lean_dec(v_b_3215_);
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
v___jp_3234_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = lean_array_get_borrowed(v___x_3214_, v_xs_3226_, v_b_3215_);
lean_dec(v_b_3215_);
lean_inc_ref(v___y_3238_);
lean_inc(v___x_3240_);
v___x_3241_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3216_, v_positions_3217_, v_recFnNames_3218_, v_containsRecFn_3219_, v___x_3240_, v_altBody_3227_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v___x_3243_ = 1;
v___x_3244_ = l_Lean_Meta_mkLambdaFVars(v_xs_3226_, v_a_3242_, v___x_3220_, v_a_3221_, v___x_3220_, v_a_3221_, v___x_3243_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec_ref(v_xs_3226_);
return v___x_3244_;
}
else
{
lean_dec_ref(v_xs_3226_);
return v___x_3241_;
}
}
v___jp_3245_:
{
lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3251_ = lean_array_get_size(v_xs_3226_);
v___x_3252_ = lean_nat_dec_eq(v___x_3251_, v___x_3222_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec_ref(v_altBody_3227_);
lean_dec_ref(v_xs_3226_);
lean_dec_ref(v_containsRecFn_3219_);
lean_dec_ref(v_recFnNames_3218_);
lean_dec_ref(v_positions_3217_);
lean_dec_ref(v_recArgInfos_3216_);
lean_dec(v_b_3215_);
v___x_3253_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3254_ = l_Lean_indentExpr(v_a_3223_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = l_Lean_indentExpr(v_e_3224_);
v___x_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3259_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
lean_dec_ref(v_e_3224_);
lean_dec_ref(v_a_3223_);
v___y_3235_ = v___y_3246_;
v___y_3236_ = v___y_3247_;
v___y_3237_ = v___y_3248_;
v___y_3238_ = v___y_3249_;
v___y_3239_ = v___y_3250_;
goto v___jp_3234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v___x_3297_ = _args[0];
lean_object* v_b_3298_ = _args[1];
lean_object* v_recArgInfos_3299_ = _args[2];
lean_object* v_positions_3300_ = _args[3];
lean_object* v_recFnNames_3301_ = _args[4];
lean_object* v_containsRecFn_3302_ = _args[5];
lean_object* v___x_3303_ = _args[6];
lean_object* v_a_3304_ = _args[7];
lean_object* v___x_3305_ = _args[8];
lean_object* v_a_3306_ = _args[9];
lean_object* v_e_3307_ = _args[10];
lean_object* v___x_3308_ = _args[11];
lean_object* v_xs_3309_ = _args[12];
lean_object* v_altBody_3310_ = _args[13];
lean_object* v___y_3311_ = _args[14];
lean_object* v___y_3312_ = _args[15];
lean_object* v___y_3313_ = _args[16];
lean_object* v___y_3314_ = _args[17];
lean_object* v___y_3315_ = _args[18];
lean_object* v___y_3316_ = _args[19];
_start:
{
uint8_t v___x_28537__boxed_3317_; uint8_t v_a_28538__boxed_3318_; lean_object* v_res_3319_; 
v___x_28537__boxed_3317_ = lean_unbox(v___x_3303_);
v_a_28538__boxed_3318_ = lean_unbox(v_a_3304_);
v_res_3319_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3297_, v_b_3298_, v_recArgInfos_3299_, v_positions_3300_, v_recFnNames_3301_, v_containsRecFn_3302_, v___x_28537__boxed_3317_, v_a_28538__boxed_3318_, v___x_3305_, v_a_3306_, v_e_3307_, v___x_3308_, v_xs_3309_, v_altBody_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec(v___x_3305_);
lean_dec_ref(v___x_3297_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3320_, lean_object* v_positions_3321_, lean_object* v_recFnNames_3322_, lean_object* v_containsRecFn_3323_, uint8_t v_a_3324_, lean_object* v_e_3325_, lean_object* v_as_3326_, lean_object* v_bs_3327_, lean_object* v_i_3328_, lean_object* v_cs_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3336_ = lean_array_get_size(v_as_3326_);
v___x_3337_ = lean_nat_dec_lt(v_i_3328_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
lean_dec(v_i_3328_);
lean_dec_ref(v_e_3325_);
lean_dec_ref(v_containsRecFn_3323_);
lean_dec_ref(v_recFnNames_3322_);
lean_dec_ref(v_positions_3321_);
lean_dec_ref(v_recArgInfos_3320_);
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_cs_3329_);
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; uint8_t v___x_3340_; 
v___x_3339_ = lean_array_get_size(v_bs_3327_);
v___x_3340_ = lean_nat_dec_lt(v_i_3328_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
lean_dec(v_i_3328_);
lean_dec_ref(v_e_3325_);
lean_dec_ref(v_containsRecFn_3323_);
lean_dec_ref(v_recFnNames_3322_);
lean_dec_ref(v_positions_3321_);
lean_dec_ref(v_recArgInfos_3320_);
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_cs_3329_);
return v___x_3341_;
}
else
{
lean_object* v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v_a_3345_; lean_object* v_b_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___f_3351_; lean_object* v___x_3352_; 
v___x_3342_ = l_Lean_instInhabitedExpr;
v___x_3343_ = 0;
v___x_3344_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3345_ = lean_array_fget_borrowed(v_as_3326_, v_i_3328_);
v_b_3346_ = lean_array_fget_borrowed(v_bs_3327_, v_i_3328_);
v___x_3347_ = lean_unsigned_to_nat(1u);
v___x_3348_ = lean_nat_add(v_b_3346_, v___x_3347_);
v___x_3349_ = lean_box(v___x_3343_);
v___x_3350_ = lean_box(v_a_3324_);
lean_inc_ref(v_e_3325_);
lean_inc_n(v_a_3345_, 2);
lean_inc(v___x_3348_);
lean_inc_ref(v_containsRecFn_3323_);
lean_inc_ref(v_recFnNames_3322_);
lean_inc_ref(v_positions_3321_);
lean_inc_ref(v_recArgInfos_3320_);
lean_inc(v_b_3346_);
v___f_3351_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 20, 12);
lean_closure_set(v___f_3351_, 0, v___x_3342_);
lean_closure_set(v___f_3351_, 1, v_b_3346_);
lean_closure_set(v___f_3351_, 2, v_recArgInfos_3320_);
lean_closure_set(v___f_3351_, 3, v_positions_3321_);
lean_closure_set(v___f_3351_, 4, v_recFnNames_3322_);
lean_closure_set(v___f_3351_, 5, v_containsRecFn_3323_);
lean_closure_set(v___f_3351_, 6, v___x_3349_);
lean_closure_set(v___f_3351_, 7, v___x_3350_);
lean_closure_set(v___f_3351_, 8, v___x_3348_);
lean_closure_set(v___f_3351_, 9, v_a_3345_);
lean_closure_set(v___f_3351_, 10, v_e_3325_);
lean_closure_set(v___f_3351_, 11, v___x_3344_);
v___x_3352_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3345_, v___x_3348_, v___f_3351_, v___x_3343_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___x_3352_, 1);
v___x_3354_ = lean_nat_add(v_i_3328_, v___x_3347_);
lean_dec(v_i_3328_);
v___x_3355_ = lean_array_push(v_cs_3329_, v_a_3353_);
v_i_3328_ = v___x_3354_;
v_cs_3329_ = v___x_3355_;
goto _start;
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref(v_cs_3329_);
lean_dec(v_i_3328_);
lean_dec_ref(v_e_3325_);
lean_dec_ref(v_containsRecFn_3323_);
lean_dec_ref(v_recFnNames_3322_);
lean_dec_ref(v_positions_3321_);
lean_dec_ref(v_recArgInfos_3320_);
v_a_3357_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3352_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3352_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
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
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3367_ = l_Lean_stringToMessageData(v___x_3366_);
return v___x_3367_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3370_ = l_Lean_stringToMessageData(v___x_3369_);
return v___x_3370_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3373_ = l_Lean_stringToMessageData(v___x_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3374_, lean_object* v_positions_3375_, lean_object* v_recFnNames_3376_, lean_object* v_containsRecFn_3377_, lean_object* v_below_3378_, lean_object* v_e_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_e_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___x_3399_; 
lean_inc_ref(v_containsRecFn_3377_);
lean_inc(v_a_3384_);
lean_inc_ref(v_a_3383_);
lean_inc(v_a_3382_);
lean_inc_ref(v_a_3381_);
lean_inc(v_a_3380_);
lean_inc_ref(v_e_3379_);
v___x_3399_ = lean_apply_7(v_containsRecFn_3377_, v_e_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, lean_box(0));
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3613_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3613_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3613_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_unbox(v_a_3400_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3406_; 
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v_e_3379_);
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_e_3379_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
else
{
uint8_t v___x_3408_; 
lean_del_object(v___x_3402_);
v___x_3408_ = 0;
switch(lean_obj_tag(v_e_3379_))
{
case 6:
{
lean_object* v_binderName_3409_; lean_object* v_binderType_3410_; lean_object* v_body_3411_; uint8_t v_binderInfo_3412_; lean_object* v___x_3413_; 
v_binderName_3409_ = lean_ctor_get(v_e_3379_, 0);
lean_inc(v_binderName_3409_);
v_binderType_3410_ = lean_ctor_get(v_e_3379_, 1);
lean_inc_ref(v_binderType_3410_);
v_body_3411_ = lean_ctor_get(v_e_3379_, 2);
lean_inc_ref(v_body_3411_);
v_binderInfo_3412_ = lean_ctor_get_uint8(v_e_3379_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3379_, 3);
lean_inc_ref(v_a_3383_);
lean_inc_ref(v_below_3378_);
lean_inc_ref(v_containsRecFn_3377_);
lean_inc_ref(v_recFnNames_3376_);
lean_inc_ref(v_positions_3375_);
lean_inc_ref(v_recArgInfos_3374_);
v___x_3413_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3374_, v_positions_3375_, v_recFnNames_3376_, v_containsRecFn_3377_, v_below_3378_, v_binderType_3410_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; lean_object* v___f_3416_; uint8_t v___x_3417_; lean_object* v___x_3418_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v___x_3415_ = lean_box(v___x_3408_);
v___f_3416_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3416_, 0, v_body_3411_);
lean_closure_set(v___f_3416_, 1, v_recArgInfos_3374_);
lean_closure_set(v___f_3416_, 2, v_positions_3375_);
lean_closure_set(v___f_3416_, 3, v_recFnNames_3376_);
lean_closure_set(v___f_3416_, 4, v_containsRecFn_3377_);
lean_closure_set(v___f_3416_, 5, v_below_3378_);
lean_closure_set(v___f_3416_, 6, v___x_3415_);
lean_closure_set(v___f_3416_, 7, v_a_3400_);
v___x_3417_ = 0;
v___x_3418_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3409_, v_binderInfo_3412_, v_a_3414_, v___f_3416_, v___x_3417_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec_ref(v_a_3383_);
return v___x_3418_;
}
else
{
lean_dec_ref(v_body_3411_);
lean_dec(v_binderName_3409_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
return v___x_3413_;
}
}
case 7:
{
lean_object* v_binderName_3419_; lean_object* v_binderType_3420_; lean_object* v_body_3421_; uint8_t v_binderInfo_3422_; lean_object* v___x_3423_; 
v_binderName_3419_ = lean_ctor_get(v_e_3379_, 0);
lean_inc(v_binderName_3419_);
v_binderType_3420_ = lean_ctor_get(v_e_3379_, 1);
lean_inc_ref(v_binderType_3420_);
v_body_3421_ = lean_ctor_get(v_e_3379_, 2);
lean_inc_ref(v_body_3421_);
v_binderInfo_3422_ = lean_ctor_get_uint8(v_e_3379_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3379_, 3);
lean_inc_ref(v_a_3383_);
lean_inc_ref(v_below_3378_);
lean_inc_ref(v_containsRecFn_3377_);
lean_inc_ref(v_recFnNames_3376_);
lean_inc_ref(v_positions_3375_);
lean_inc_ref(v_recArgInfos_3374_);
v___x_3423_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3374_, v_positions_3375_, v_recFnNames_3376_, v_containsRecFn_3377_, v_below_3378_, v_binderType_3420_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; lean_object* v___f_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = lean_box(v___x_3408_);
v___f_3426_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3426_, 0, v_body_3421_);
lean_closure_set(v___f_3426_, 1, v_recArgInfos_3374_);
lean_closure_set(v___f_3426_, 2, v_positions_3375_);
lean_closure_set(v___f_3426_, 3, v_recFnNames_3376_);
lean_closure_set(v___f_3426_, 4, v_containsRecFn_3377_);
lean_closure_set(v___f_3426_, 5, v_below_3378_);
lean_closure_set(v___f_3426_, 6, v___x_3425_);
lean_closure_set(v___f_3426_, 7, v_a_3400_);
v___x_3427_ = 0;
v___x_3428_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3419_, v_binderInfo_3422_, v_a_3424_, v___f_3426_, v___x_3427_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec_ref(v_a_3383_);
return v___x_3428_;
}
else
{
lean_dec_ref(v_body_3421_);
lean_dec(v_binderName_3419_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
return v___x_3423_;
}
}
case 8:
{
lean_object* v_declName_3429_; lean_object* v_type_3430_; lean_object* v_value_3431_; lean_object* v_body_3432_; uint8_t v_nondep_3433_; lean_object* v___x_3434_; 
lean_dec(v_a_3400_);
v_declName_3429_ = lean_ctor_get(v_e_3379_, 0);
lean_inc(v_declName_3429_);
v_type_3430_ = lean_ctor_get(v_e_3379_, 1);
lean_inc_ref(v_type_3430_);
v_value_3431_ = lean_ctor_get(v_e_3379_, 2);
lean_inc_ref(v_value_3431_);
v_body_3432_ = lean_ctor_get(v_e_3379_, 3);
lean_inc_ref(v_body_3432_);
v_nondep_3433_ = lean_ctor_get_uint8(v_e_3379_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3379_, 4);
lean_inc_ref(v_a_3383_);
lean_inc_ref(v_below_3378_);
lean_inc_ref(v_containsRecFn_3377_);
lean_inc_ref(v_recFnNames_3376_);
lean_inc_ref(v_positions_3375_);
lean_inc_ref(v_recArgInfos_3374_);
v___x_3434_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3374_, v_positions_3375_, v_recFnNames_3376_, v_containsRecFn_3377_, v_below_3378_, v_type_3430_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
lean_inc_ref(v_a_3383_);
lean_inc_ref(v_below_3378_);
lean_inc_ref(v_containsRecFn_3377_);
lean_inc_ref(v_recFnNames_3376_);
lean_inc_ref(v_positions_3375_);
lean_inc_ref(v_recArgInfos_3374_);
v___x_3436_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3374_, v_positions_3375_, v_recFnNames_3376_, v_containsRecFn_3377_, v_below_3378_, v_value_3431_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___f_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
v___f_3438_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3438_, 0, v_body_3432_);
lean_closure_set(v___f_3438_, 1, v_recArgInfos_3374_);
lean_closure_set(v___f_3438_, 2, v_positions_3375_);
lean_closure_set(v___f_3438_, 3, v_recFnNames_3376_);
lean_closure_set(v___f_3438_, 4, v_containsRecFn_3377_);
lean_closure_set(v___f_3438_, 5, v_below_3378_);
v___x_3439_ = 0;
v___x_3440_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3429_, v_a_3435_, v_a_3437_, v___f_3438_, v_nondep_3433_, v___x_3439_, v___x_3408_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec_ref(v_a_3383_);
return v___x_3440_;
}
else
{
lean_dec(v_a_3435_);
lean_dec_ref(v_body_3432_);
lean_dec(v_declName_3429_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
return v___x_3436_;
}
}
else
{
lean_dec_ref(v_body_3432_);
lean_dec_ref(v_value_3431_);
lean_dec(v_declName_3429_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
return v___x_3434_;
}
}
case 10:
{
lean_object* v_data_3441_; lean_object* v_expr_3442_; lean_object* v___x_3443_; 
lean_dec(v_a_3400_);
v_data_3441_ = lean_ctor_get(v_e_3379_, 0);
lean_inc(v_data_3441_);
v_expr_3442_ = lean_ctor_get(v_e_3379_, 1);
lean_inc_ref(v_expr_3442_);
v___x_3443_ = l_Lean_getRecAppSyntax_x3f(v_e_3379_);
lean_dec_ref_known(v_e_3379_, 2);
if (lean_obj_tag(v___x_3443_) == 1)
{
lean_object* v_val_3444_; lean_object* v_toCold_3445_; lean_object* v_currRecDepth_3446_; lean_object* v_ref_3447_; uint8_t v_diag_3448_; uint8_t v_suppressElabErrors_3449_; lean_object* v_ref_3450_; lean_object* v___x_3451_; 
lean_dec(v_data_3441_);
v_val_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_val_3444_);
lean_dec_ref_known(v___x_3443_, 1);
v_toCold_3445_ = lean_ctor_get(v_a_3383_, 0);
lean_inc_ref(v_toCold_3445_);
v_currRecDepth_3446_ = lean_ctor_get(v_a_3383_, 1);
lean_inc(v_currRecDepth_3446_);
v_ref_3447_ = lean_ctor_get(v_a_3383_, 2);
lean_inc(v_ref_3447_);
v_diag_3448_ = lean_ctor_get_uint8(v_a_3383_, sizeof(void*)*3);
v_suppressElabErrors_3449_ = lean_ctor_get_uint8(v_a_3383_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_3383_);
v_ref_3450_ = l_Lean_replaceRef(v_val_3444_, v_ref_3447_);
lean_dec(v_ref_3447_);
lean_dec(v_val_3444_);
v___x_3451_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3451_, 0, v_toCold_3445_);
lean_ctor_set(v___x_3451_, 1, v_currRecDepth_3446_);
lean_ctor_set(v___x_3451_, 2, v_ref_3450_);
lean_ctor_set_uint8(v___x_3451_, sizeof(void*)*3, v_diag_3448_);
lean_ctor_set_uint8(v___x_3451_, sizeof(void*)*3 + 1, v_suppressElabErrors_3449_);
v_e_3379_ = v_expr_3442_;
v_a_3383_ = v___x_3451_;
goto _start;
}
else
{
lean_object* v___x_3453_; 
lean_dec(v___x_3443_);
v___x_3453_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3374_, v_positions_3375_, v_recFnNames_3376_, v_containsRecFn_3377_, v_below_3378_, v_expr_3442_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3462_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3462_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3462_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3458_ = l_Lean_mkMData(v_data_3441_, v_a_3454_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3458_);
v___x_3460_ = v___x_3456_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
else
{
lean_dec(v_data_3441_);
return v___x_3453_;
}
}
}
case 11:
{
lean_object* v_typeName_3463_; lean_object* v_idx_3464_; lean_object* v_struct_3465_; lean_object* v___x_3466_; 
lean_dec(v_a_3400_);
v_typeName_3463_ = lean_ctor_get(v_e_3379_, 0);
lean_inc(v_typeName_3463_);
v_idx_3464_ = lean_ctor_get(v_e_3379_, 1);
lean_inc(v_idx_3464_);
v_struct_3465_ = lean_ctor_get(v_e_3379_, 2);
lean_inc_ref(v_struct_3465_);
lean_dec_ref_known(v_e_3379_, 3);
v___x_3466_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3374_, v_positions_3375_, v_recFnNames_3376_, v_containsRecFn_3377_, v_below_3378_, v_struct_3465_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = l_Lean_mkProj(v_typeName_3463_, v_idx_3464_, v_a_3467_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
else
{
lean_dec(v_idx_3464_);
lean_dec(v_typeName_3463_);
return v___x_3466_;
}
}
case 5:
{
uint8_t v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = lean_unbox(v_a_3400_);
lean_inc_ref(v_e_3379_);
v___x_3477_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3379_, v___x_3476_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
if (lean_obj_tag(v_a_3478_) == 0)
{
lean_dec(v_a_3400_);
v_e_3387_ = v_e_3379_;
v___y_3388_ = v_a_3380_;
v___y_3389_ = v_a_3381_;
v___y_3390_ = v_a_3382_;
v___y_3391_ = v_a_3383_;
v___y_3392_ = v_a_3384_;
goto v___jp_3386_;
}
else
{
lean_object* v_val_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; 
v_val_3479_ = lean_ctor_get(v_a_3478_, 0);
lean_inc(v_val_3479_);
lean_dec_ref_known(v_a_3478_, 1);
v___x_3480_ = lean_unsigned_to_nat(0u);
v___x_3481_ = lean_array_get_size(v_recArgInfos_3374_);
v___x_3482_ = lean_nat_dec_lt(v___x_3480_, v___x_3481_);
if (v___x_3482_ == 0)
{
lean_dec(v_val_3479_);
lean_dec(v_a_3400_);
v_e_3387_ = v_e_3379_;
v___y_3388_ = v_a_3380_;
v___y_3389_ = v_a_3381_;
v___y_3390_ = v_a_3382_;
v___y_3391_ = v_a_3383_;
v___y_3392_ = v_a_3384_;
goto v___jp_3386_;
}
else
{
if (v___x_3482_ == 0)
{
lean_dec(v_val_3479_);
lean_dec(v_a_3400_);
v_e_3387_ = v_e_3379_;
v___y_3388_ = v_a_3380_;
v___y_3389_ = v_a_3381_;
v___y_3390_ = v_a_3382_;
v___y_3391_ = v_a_3383_;
v___y_3392_ = v_a_3384_;
goto v___jp_3386_;
}
else
{
size_t v___x_3483_; size_t v___x_3484_; uint8_t v___x_3485_; 
v___x_3483_ = ((size_t)0ULL);
v___x_3484_ = lean_usize_of_nat(v___x_3481_);
v___x_3485_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3379_, v_recArgInfos_3374_, v___x_3483_, v___x_3484_);
if (v___x_3485_ == 0)
{
lean_dec(v_val_3479_);
lean_dec(v_a_3400_);
v_e_3387_ = v_e_3379_;
v___y_3388_ = v_a_3380_;
v___y_3389_ = v_a_3381_;
v___y_3390_ = v_a_3382_;
v___y_3391_ = v_a_3383_;
v___y_3392_ = v_a_3384_;
goto v___jp_3386_;
}
else
{
lean_object* v_toCold_3486_; lean_object* v_inheritedTraceOptions_3487_; lean_object* v___x_3488_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___x_3559_; 
v_toCold_3486_ = lean_ctor_get(v_a_3383_, 0);
v_inheritedTraceOptions_3487_ = lean_ctor_get(v_toCold_3486_, 11);
v___x_3488_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3559_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3488_, v_inheritedTraceOptions_3487_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; uint8_t v___x_3561_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___x_3561_ = lean_unbox(v_a_3560_);
lean_dec(v_a_3560_);
if (v___x_3561_ == 0)
{
v___y_3490_ = v_a_3380_;
v___y_3491_ = v_a_3381_;
v___y_3492_ = v_a_3382_;
v___y_3493_ = v_a_3383_;
v___y_3494_ = v_a_3384_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3562_; 
lean_inc(v_a_3384_);
lean_inc_ref(v_a_3383_);
lean_inc(v_a_3382_);
lean_inc_ref(v_a_3381_);
lean_inc_ref(v_below_3378_);
v___x_3562_ = lean_infer_type(v_below_3378_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3562_, 1);
v___x_3564_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3378_);
v___x_3565_ = l_Lean_MessageData_ofExpr(v_below_3378_);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_MessageData_ofExpr(v_a_3563_);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3488_, v___x_3570_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_dec_ref_known(v___x_3571_, 1);
v___y_3490_ = v_a_3380_;
v___y_3491_ = v_a_3381_;
v___y_3492_ = v_a_3382_;
v___y_3493_ = v_a_3383_;
v___y_3494_ = v_a_3384_;
goto v___jp_3489_;
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v_val_3479_);
lean_dec_ref_known(v_e_3379_, 2);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_dec(v_val_3479_);
lean_dec_ref_known(v_e_3379_, 2);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
return v___x_3562_;
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec(v_val_3479_);
lean_dec_ref_known(v_e_3379_, 2);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
v_a_3580_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3559_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3559_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
v___jp_3489_:
{
lean_object* v___x_3495_; 
lean_inc_ref(v_below_3378_);
v___x_3495_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3479_, v_below_3378_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
if (lean_obj_tag(v_a_3496_) == 1)
{
lean_object* v_val_3497_; lean_object* v_toMatcherInfo_3498_; lean_object* v_matcherName_3499_; lean_object* v_matcherLevels_3500_; lean_object* v_params_3501_; lean_object* v_motive_3502_; lean_object* v_discrs_3503_; lean_object* v_alts_3504_; lean_object* v_remaining_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; lean_object* v___x_3509_; 
lean_dec_ref(v_below_3378_);
v_val_3497_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_val_3497_);
lean_dec_ref_known(v_a_3496_, 1);
v_toMatcherInfo_3498_ = lean_ctor_get(v_val_3497_, 0);
lean_inc_ref(v_toMatcherInfo_3498_);
v_matcherName_3499_ = lean_ctor_get(v_val_3497_, 1);
lean_inc(v_matcherName_3499_);
v_matcherLevels_3500_ = lean_ctor_get(v_val_3497_, 2);
lean_inc_ref(v_matcherLevels_3500_);
v_params_3501_ = lean_ctor_get(v_val_3497_, 3);
lean_inc_ref(v_params_3501_);
v_motive_3502_ = lean_ctor_get(v_val_3497_, 4);
lean_inc_ref(v_motive_3502_);
v_discrs_3503_ = lean_ctor_get(v_val_3497_, 5);
lean_inc_ref(v_discrs_3503_);
v_alts_3504_ = lean_ctor_get(v_val_3497_, 6);
lean_inc_ref(v_alts_3504_);
v_remaining_3505_ = lean_ctor_get(v_val_3497_, 7);
lean_inc_ref(v_remaining_3505_);
v___x_3506_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3497_);
v___x_3507_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3508_ = lean_unbox(v_a_3400_);
lean_dec(v_a_3400_);
v___x_3509_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3374_, v_positions_3375_, v_recFnNames_3376_, v_containsRecFn_3377_, v___x_3508_, v_e_3379_, v_alts_3504_, v___x_3506_, v___x_3480_, v___x_3507_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v_alts_3504_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3519_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3519_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3519_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3514_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3514_, 0, v_toMatcherInfo_3498_);
lean_ctor_set(v___x_3514_, 1, v_matcherName_3499_);
lean_ctor_set(v___x_3514_, 2, v_matcherLevels_3500_);
lean_ctor_set(v___x_3514_, 3, v_params_3501_);
lean_ctor_set(v___x_3514_, 4, v_motive_3502_);
lean_ctor_set(v___x_3514_, 5, v_discrs_3503_);
lean_ctor_set(v___x_3514_, 6, v_a_3510_);
lean_ctor_set(v___x_3514_, 7, v_remaining_3505_);
v___x_3515_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3514_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3515_);
v___x_3517_ = v___x_3512_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_remaining_3505_);
lean_dec_ref(v_discrs_3503_);
lean_dec_ref(v_motive_3502_);
lean_dec_ref(v_params_3501_);
lean_dec_ref(v_matcherLevels_3500_);
lean_dec(v_matcherName_3499_);
lean_dec_ref(v_toMatcherInfo_3498_);
v_a_3520_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3509_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3509_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_toCold_3528_; lean_object* v_inheritedTraceOptions_3529_; lean_object* v___x_3530_; 
lean_dec(v_a_3496_);
lean_dec(v_a_3400_);
v_toCold_3528_ = lean_ctor_get(v___y_3493_, 0);
v_inheritedTraceOptions_3529_ = lean_ctor_get(v_toCold_3528_, 11);
v___x_3530_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3488_, v_inheritedTraceOptions_3529_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; uint8_t v___x_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v___x_3532_ = lean_unbox(v_a_3531_);
lean_dec(v_a_3531_);
if (v___x_3532_ == 0)
{
v_e_3387_ = v_e_3379_;
v___y_3388_ = v___y_3490_;
v___y_3389_ = v___y_3491_;
v___y_3390_ = v___y_3492_;
v___y_3391_ = v___y_3493_;
v___y_3392_ = v___y_3494_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3534_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3488_, v___x_3533_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_dec_ref_known(v___x_3534_, 1);
v_e_3387_ = v_e_3379_;
v___y_3388_ = v___y_3490_;
v___y_3389_ = v___y_3491_;
v___y_3390_ = v___y_3492_;
v___y_3391_ = v___y_3493_;
v___y_3392_ = v___y_3494_;
goto v___jp_3386_;
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec_ref(v___y_3493_);
lean_dec_ref_known(v_e_3379_, 2);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec_ref(v___y_3493_);
lean_dec_ref_known(v_e_3379_, 2);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
v_a_3543_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3530_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3530_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v___y_3493_);
lean_dec_ref_known(v_e_3379_, 2);
lean_dec(v_a_3400_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
v_a_3551_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3495_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3495_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
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
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref_known(v_e_3379_, 2);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
v_a_3588_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3477_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3477_);
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
default: 
{
lean_object* v___x_3596_; 
lean_dec(v_a_3400_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
lean_inc_ref(v_e_3379_);
v___x_3596_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3376_, v_e_3379_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec_ref(v_a_3383_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3596_, 0);
lean_dec(v_unused_3604_);
v___x_3598_ = v___x_3596_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_dec(v___x_3596_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v_e_3379_);
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_e_3379_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec_ref(v_e_3379_);
v_a_3605_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3596_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3596_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
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
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_e_3379_);
lean_dec_ref(v_below_3378_);
lean_dec_ref(v_containsRecFn_3377_);
lean_dec_ref(v_recFnNames_3376_);
lean_dec_ref(v_positions_3375_);
lean_dec_ref(v_recArgInfos_3374_);
v_a_3614_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3399_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3399_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
v___jp_3386_:
{
lean_object* v_dummy_3393_; lean_object* v_nargs_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_dummy_3393_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3394_ = l_Lean_Expr_getAppNumArgs(v_e_3387_);
lean_inc(v_nargs_3394_);
v___x_3395_ = lean_mk_array(v_nargs_3394_, v_dummy_3393_);
v___x_3396_ = lean_unsigned_to_nat(1u);
v___x_3397_ = lean_nat_sub(v_nargs_3394_, v___x_3396_);
lean_dec(v_nargs_3394_);
lean_inc_ref(v_e_3387_);
v___x_3398_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3374_, v_positions_3375_, v_recFnNames_3376_, v_containsRecFn_3377_, v_below_3378_, v_e_3387_, v_e_3387_, v___x_3395_, v___x_3397_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec_ref(v___y_3391_);
return v___x_3398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3622_, lean_object* v_recArgInfos_3623_, lean_object* v_positions_3624_, lean_object* v_recFnNames_3625_, lean_object* v_containsRecFn_3626_, lean_object* v_below_3627_, lean_object* v_x_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_expr_instantiate1(v_body_3622_, v_x_3628_);
lean_inc_ref(v___y_3632_);
v___x_3636_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3623_, v_positions_3624_, v_recFnNames_3625_, v_containsRecFn_3626_, v_below_3627_, v___x_3635_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3637_, lean_object* v_positions_3638_, lean_object* v_recFnNames_3639_, lean_object* v_containsRecFn_3640_, lean_object* v_below_3641_, lean_object* v_sz_3642_, lean_object* v_i_3643_, lean_object* v_bs_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
size_t v_sz_boxed_3651_; size_t v_i_boxed_3652_; lean_object* v_res_3653_; 
v_sz_boxed_3651_ = lean_unbox_usize(v_sz_3642_);
lean_dec(v_sz_3642_);
v_i_boxed_3652_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_res_3653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3637_, v_positions_3638_, v_recFnNames_3639_, v_containsRecFn_3640_, v_below_3641_, v_sz_boxed_3651_, v_i_boxed_3652_, v_bs_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3654_, lean_object* v_positions_3655_, lean_object* v_recFnNames_3656_, lean_object* v_containsRecFn_3657_, lean_object* v_a_3658_, lean_object* v_e_3659_, lean_object* v_as_3660_, lean_object* v_bs_3661_, lean_object* v_i_3662_, lean_object* v_cs_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_a_28495__boxed_3670_; lean_object* v_res_3671_; 
v_a_28495__boxed_3670_ = lean_unbox(v_a_3658_);
v_res_3671_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3654_, v_positions_3655_, v_recFnNames_3656_, v_containsRecFn_3657_, v_a_28495__boxed_3670_, v_e_3659_, v_as_3660_, v_bs_3661_, v_i_3662_, v_cs_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v_bs_3661_);
lean_dec_ref(v_as_3660_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3672_, lean_object* v_positions_3673_, lean_object* v_recFnNames_3674_, lean_object* v_containsRecFn_3675_, lean_object* v_below_3676_, lean_object* v_e_3677_, lean_object* v_x_3678_, lean_object* v_x_3679_, lean_object* v_x_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3672_, v_positions_3673_, v_recFnNames_3674_, v_containsRecFn_3675_, v_below_3676_, v_e_3677_, v_x_3678_, v_x_3679_, v_x_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3688_, lean_object* v_positions_3689_, lean_object* v_recFnNames_3690_, lean_object* v_containsRecFn_3691_, lean_object* v_below_3692_, lean_object* v_e_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3688_, v_positions_3689_, v_recFnNames_3690_, v_containsRecFn_3691_, v_below_3692_, v_e_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
lean_dec(v_a_3698_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3701_, lean_object* v_msg_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3702_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3710_, lean_object* v_msg_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3710_, v_msg_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3719_, lean_object* v_name_3720_, lean_object* v_type_3721_, lean_object* v_val_3722_, lean_object* v_k_3723_, uint8_t v_nondep_3724_, uint8_t v_kind_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3720_, v_type_3721_, v_val_3722_, v_k_3723_, v_nondep_3724_, v_kind_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3733_, lean_object* v_name_3734_, lean_object* v_type_3735_, lean_object* v_val_3736_, lean_object* v_k_3737_, lean_object* v_nondep_3738_, lean_object* v_kind_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
uint8_t v_nondep_boxed_3746_; uint8_t v_kind_boxed_3747_; lean_object* v_res_3748_; 
v_nondep_boxed_3746_ = lean_unbox(v_nondep_3738_);
v_kind_boxed_3747_ = lean_unbox(v_kind_3739_);
v_res_3748_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3733_, v_name_3734_, v_type_3735_, v_val_3736_, v_k_3737_, v_nondep_boxed_3746_, v_kind_boxed_3747_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3749_, v___y_3754_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3765_, lean_object* v_msg_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3765_, v_msg_3766_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3774_, lean_object* v_msg_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3774_, v_msg_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3783_, lean_object* v_constName_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3792_, lean_object* v_constName_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3792_, v_constName_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3801_, lean_object* v_ref_3802_, lean_object* v_constName_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3802_, v_constName_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3811_, lean_object* v_ref_3812_, lean_object* v_constName_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3811_, v_ref_3812_, v_constName_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec(v_ref_3812_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3821_, lean_object* v_ref_3822_, lean_object* v_msg_3823_, lean_object* v_declHint_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3822_, v_msg_3823_, v_declHint_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3832_, lean_object* v_ref_3833_, lean_object* v_msg_3834_, lean_object* v_declHint_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3832_, v_ref_3833_, v_msg_3834_, v_declHint_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v_ref_3833_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3843_, lean_object* v_declHint_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3843_, v_declHint_3844_, v___y_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3852_, lean_object* v_declHint_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3852_, v_declHint_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3861_, lean_object* v_ref_3862_, lean_object* v_msg_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3862_, v_msg_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3871_, lean_object* v_ref_3872_, lean_object* v_msg_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3871_, v_ref_3872_, v_msg_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec(v_ref_3872_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3881_, lean_object* v_e_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v_fst_3891_; lean_object* v_snd_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3889_ = lean_st_ref_take(v___y_3883_);
v___x_3890_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3881_, v_e_3882_, v___x_3889_);
v_fst_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_fst_3891_);
v_snd_3892_ = lean_ctor_get(v___x_3890_, 1);
lean_inc(v_snd_3892_);
lean_dec_ref(v___x_3890_);
v___x_3893_ = lean_st_ref_put(v___y_3883_, v_snd_3892_);
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v_fst_3891_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3895_, lean_object* v_e_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3895_, v_e_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v_recFnNames_3895_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3904_, size_t v_i_3905_, lean_object* v_bs_3906_){
_start:
{
uint8_t v___x_3907_; 
v___x_3907_ = lean_usize_dec_lt(v_i_3905_, v_sz_3904_);
if (v___x_3907_ == 0)
{
return v_bs_3906_;
}
else
{
lean_object* v_v_3908_; lean_object* v_fnName_3909_; lean_object* v___x_3910_; lean_object* v_bs_x27_3911_; size_t v___x_3912_; size_t v___x_3913_; lean_object* v___x_3914_; 
v_v_3908_ = lean_array_uget_borrowed(v_bs_3906_, v_i_3905_);
v_fnName_3909_ = lean_ctor_get(v_v_3908_, 0);
lean_inc(v_fnName_3909_);
v___x_3910_ = lean_unsigned_to_nat(0u);
v_bs_x27_3911_ = lean_array_uset(v_bs_3906_, v_i_3905_, v___x_3910_);
v___x_3912_ = ((size_t)1ULL);
v___x_3913_ = lean_usize_add(v_i_3905_, v___x_3912_);
v___x_3914_ = lean_array_uset(v_bs_x27_3911_, v_i_3905_, v_fnName_3909_);
v_i_3905_ = v___x_3913_;
v_bs_3906_ = v___x_3914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3916_, lean_object* v_i_3917_, lean_object* v_bs_3918_){
_start:
{
size_t v_sz_boxed_3919_; size_t v_i_boxed_3920_; lean_object* v_res_3921_; 
v_sz_boxed_3919_ = lean_unbox_usize(v_sz_3916_);
lean_dec(v_sz_3916_);
v_i_boxed_3920_ = lean_unbox_usize(v_i_3917_);
lean_dec(v_i_3917_);
v_res_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3919_, v_i_boxed_3920_, v_bs_3918_);
return v_res_3921_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = lean_box(0);
v___x_3923_ = lean_unsigned_to_nat(16u);
v___x_3924_ = lean_mk_array(v___x_3923_, v___x_3922_);
return v___x_3924_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v___x_3925_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3928_, lean_object* v_positions_3929_, lean_object* v_below_3930_, lean_object* v_e_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; size_t v_sz_3939_; size_t v___x_3940_; lean_object* v_recFnNames_3941_; lean_object* v_containsRecFn_3942_; lean_object* v___x_3943_; 
v___x_3937_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3938_ = lean_st_mk_ref(v___x_3937_);
v_sz_3939_ = lean_array_size(v_recArgInfos_3928_);
v___x_3940_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3928_);
v_recFnNames_3941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3939_, v___x_3940_, v_recArgInfos_3928_);
lean_inc_ref(v_recFnNames_3941_);
v_containsRecFn_3942_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_3942_, 0, v_recFnNames_3941_);
lean_inc_ref(v_a_3934_);
v___x_3943_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3928_, v_positions_3929_, v_recFnNames_3941_, v_containsRecFn_3942_, v_below_3930_, v_e_3931_, v___x_3938_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3952_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3946_ = v___x_3943_;
v_isShared_3947_ = v_isSharedCheck_3952_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3943_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3952_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v___x_3950_; 
v___x_3948_ = lean_st_ref_get(v___x_3938_);
lean_dec(v___x_3938_);
lean_dec(v___x_3948_);
if (v_isShared_3947_ == 0)
{
v___x_3950_ = v___x_3946_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3944_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
else
{
lean_dec(v___x_3938_);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_3953_, lean_object* v_positions_3954_, lean_object* v_below_3955_, lean_object* v_e_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_3953_, v_positions_3954_, v_below_3955_, v_e_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_3963_, lean_object* v_k_3964_, uint8_t v_cleanupAnnotations_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v___f_3971_; uint8_t v___x_3972_; uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___f_3971_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3971_, 0, v_k_3964_);
v___x_3972_ = 1;
v___x_3973_ = 0;
v___x_3974_ = lean_box(0);
v___x_3975_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3963_, v___x_3972_, v___x_3973_, v___x_3972_, v___x_3973_, v___x_3974_, v___f_3971_, v_cleanupAnnotations_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
v_a_3984_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3975_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3975_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_3992_, lean_object* v_k_3993_, lean_object* v_cleanupAnnotations_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4000_; lean_object* v_res_4001_; 
v_cleanupAnnotations_boxed_4000_ = lean_unbox(v_cleanupAnnotations_3994_);
v_res_4001_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_3992_, v_k_3993_, v_cleanupAnnotations_boxed_4000_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4002_, lean_object* v_e_4003_, lean_object* v_k_4004_, uint8_t v_cleanupAnnotations_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4003_, v_k_4004_, v_cleanupAnnotations_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4012_, lean_object* v_e_4013_, lean_object* v_k_4014_, lean_object* v_cleanupAnnotations_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4021_; lean_object* v_res_4022_; 
v_cleanupAnnotations_boxed_4021_ = lean_unbox(v_cleanupAnnotations_4015_);
v_res_4022_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4012_, v_e_4013_, v_k_4014_, v_cleanupAnnotations_boxed_4021_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4023_, lean_object* v_recArgInfo_4024_, lean_object* v_xs_4025_, lean_object* v___value_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_Meta_instantiateForall(v_type_4023_, v_xs_4025_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4034_; lean_object* v_fst_4035_; lean_object* v_snd_4036_; uint8_t v___x_4037_; uint8_t v___x_4038_; uint8_t v___x_4039_; lean_object* v___x_4040_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v___x_4034_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4024_, v_xs_4025_);
v_fst_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_fst_4035_);
v_snd_4036_ = lean_ctor_get(v___x_4034_, 1);
lean_inc(v_snd_4036_);
lean_dec_ref(v___x_4034_);
v___x_4037_ = 0;
v___x_4038_ = 1;
v___x_4039_ = 1;
v___x_4040_ = l_Lean_Meta_mkForallFVars(v_snd_4036_, v_a_4033_, v___x_4037_, v___x_4038_, v___x_4038_, v___x_4039_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v_snd_4036_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = l_Lean_Meta_mkLambdaFVars(v_fst_4035_, v_a_4041_, v___x_4037_, v___x_4038_, v___x_4037_, v___x_4038_, v___x_4039_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v_fst_4035_);
return v___x_4042_;
}
else
{
lean_dec(v_fst_4035_);
return v___x_4040_;
}
}
else
{
lean_dec_ref(v_xs_4025_);
lean_dec_ref(v_recArgInfo_4024_);
return v___x_4032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4043_, lean_object* v_recArgInfo_4044_, lean_object* v_xs_4045_, lean_object* v___value_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4043_, v_recArgInfo_4044_, v_xs_4045_, v___value_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec_ref(v___value_4046_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4053_, lean_object* v_value_4054_, lean_object* v_type_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v___f_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; 
v___f_4061_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4061_, 0, v_type_4055_);
lean_closure_set(v___f_4061_, 1, v_recArgInfo_4053_);
v___x_4062_ = 0;
v___x_4063_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4054_, v___f_4061_, v___x_4062_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4064_, lean_object* v_value_4065_, lean_object* v_type_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4064_, v_value_4065_, v_type_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4073_, lean_object* v_maxFVars_x3f_4074_, lean_object* v_k_4075_, uint8_t v_cleanupAnnotations_4076_, uint8_t v_whnfType_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___f_4083_; lean_object* v___x_4084_; 
v___f_4083_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4083_, 0, v_k_4075_);
v___x_4084_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4073_, v_maxFVars_x3f_4074_, v___f_4083_, v_cleanupAnnotations_4076_, v_whnfType_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4084_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
v_a_4093_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4084_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4084_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4101_, lean_object* v_maxFVars_x3f_4102_, lean_object* v_k_4103_, lean_object* v_cleanupAnnotations_4104_, lean_object* v_whnfType_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4111_; uint8_t v_whnfType_boxed_4112_; lean_object* v_res_4113_; 
v_cleanupAnnotations_boxed_4111_ = lean_unbox(v_cleanupAnnotations_4104_);
v_whnfType_boxed_4112_ = lean_unbox(v_whnfType_4105_);
v_res_4113_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4101_, v_maxFVars_x3f_4102_, v_k_4103_, v_cleanupAnnotations_boxed_4111_, v_whnfType_boxed_4112_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4114_, lean_object* v_type_4115_, lean_object* v_maxFVars_x3f_4116_, lean_object* v_k_4117_, uint8_t v_cleanupAnnotations_4118_, uint8_t v_whnfType_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4115_, v_maxFVars_x3f_4116_, v_k_4117_, v_cleanupAnnotations_4118_, v_whnfType_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4126_, lean_object* v_type_4127_, lean_object* v_maxFVars_x3f_4128_, lean_object* v_k_4129_, lean_object* v_cleanupAnnotations_4130_, lean_object* v_whnfType_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4137_; uint8_t v_whnfType_boxed_4138_; lean_object* v_res_4139_; 
v_cleanupAnnotations_boxed_4137_ = lean_unbox(v_cleanupAnnotations_4130_);
v_whnfType_boxed_4138_ = lean_unbox(v_whnfType_4131_);
v_res_4139_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4126_, v_type_4127_, v_maxFVars_x3f_4128_, v_k_4129_, v_cleanupAnnotations_boxed_4137_, v_whnfType_boxed_4138_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4140_, lean_object* v_recArgInfos_4141_, lean_object* v_positions_4142_, lean_object* v_value_4143_, lean_object* v_fst_4144_, lean_object* v_snd_4145_, lean_object* v_below_4146_, lean_object* v_x_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4153_ = lean_unsigned_to_nat(0u);
v___x_4154_ = lean_array_get_borrowed(v___x_4140_, v_below_4146_, v___x_4153_);
lean_inc(v___x_4154_);
v___x_4155_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4141_, v_positions_4142_, v___x_4154_, v_value_4143_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; uint8_t v___x_4162_; uint8_t v___x_4163_; uint8_t v___x_4164_; lean_object* v___x_4165_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v___x_4157_ = lean_unsigned_to_nat(1u);
v___x_4158_ = lean_mk_empty_array_with_capacity(v___x_4157_);
lean_inc(v___x_4154_);
v___x_4159_ = lean_array_push(v___x_4158_, v___x_4154_);
v___x_4160_ = l_Array_append___redArg(v_fst_4144_, v___x_4159_);
lean_dec_ref(v___x_4159_);
v___x_4161_ = l_Array_append___redArg(v___x_4160_, v_snd_4145_);
v___x_4162_ = 0;
v___x_4163_ = 1;
v___x_4164_ = 1;
v___x_4165_ = l_Lean_Meta_mkLambdaFVars(v___x_4161_, v_a_4156_, v___x_4162_, v___x_4163_, v___x_4162_, v___x_4163_, v___x_4164_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec_ref(v___x_4161_);
return v___x_4165_;
}
else
{
lean_dec_ref(v_fst_4144_);
return v___x_4155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4166_, lean_object* v_recArgInfos_4167_, lean_object* v_positions_4168_, lean_object* v_value_4169_, lean_object* v_fst_4170_, lean_object* v_snd_4171_, lean_object* v_below_4172_, lean_object* v_x_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4166_, v_recArgInfos_4167_, v_positions_4168_, v_value_4169_, v_fst_4170_, v_snd_4171_, v_below_4172_, v_x_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec_ref(v_x_4173_);
lean_dec_ref(v_below_4172_);
lean_dec_ref(v_snd_4171_);
lean_dec_ref(v___x_4166_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4182_, lean_object* v_FType_4183_, lean_object* v___x_4184_, lean_object* v_recArgInfos_4185_, lean_object* v_positions_4186_, lean_object* v_xs_4187_, lean_object* v_value_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; lean_object* v_fst_4195_; lean_object* v_snd_4196_; lean_object* v___x_4197_; 
v___x_4194_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4182_, v_xs_4187_);
v_fst_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_fst_4195_);
v_snd_4196_ = lean_ctor_get(v___x_4194_, 1);
lean_inc(v_snd_4196_);
lean_dec_ref(v___x_4194_);
v___x_4197_ = l_Lean_Meta_instantiateForall(v_FType_4183_, v_fst_4195_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___f_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; lean_object* v___x_4202_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
v___f_4199_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4199_, 0, v___x_4184_);
lean_closure_set(v___f_4199_, 1, v_recArgInfos_4185_);
lean_closure_set(v___f_4199_, 2, v_positions_4186_);
lean_closure_set(v___f_4199_, 3, v_value_4188_);
lean_closure_set(v___f_4199_, 4, v_fst_4195_);
lean_closure_set(v___f_4199_, 5, v_snd_4196_);
v___x_4200_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4201_ = 0;
v___x_4202_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4198_, v___x_4200_, v___f_4199_, v___x_4201_, v___x_4201_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4202_;
}
else
{
lean_dec(v_snd_4196_);
lean_dec(v_fst_4195_);
lean_dec_ref(v_value_4188_);
lean_dec_ref(v_positions_4186_);
lean_dec_ref(v_recArgInfos_4185_);
lean_dec_ref(v___x_4184_);
return v___x_4197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4203_, lean_object* v_FType_4204_, lean_object* v___x_4205_, lean_object* v_recArgInfos_4206_, lean_object* v_positions_4207_, lean_object* v_xs_4208_, lean_object* v_value_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4203_, v_FType_4204_, v___x_4205_, v_recArgInfos_4206_, v_positions_4207_, v_xs_4208_, v_value_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4216_, lean_object* v_positions_4217_, lean_object* v_recArgInfo_4218_, lean_object* v_value_4219_, lean_object* v_FType_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v___f_4227_; uint8_t v___x_4228_; lean_object* v___x_4229_; 
v___x_4226_ = l_Lean_instInhabitedExpr;
v___f_4227_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4227_, 0, v_recArgInfo_4218_);
lean_closure_set(v___f_4227_, 1, v_FType_4220_);
lean_closure_set(v___f_4227_, 2, v___x_4226_);
lean_closure_set(v___f_4227_, 3, v_recArgInfos_4216_);
lean_closure_set(v___f_4227_, 4, v_positions_4217_);
v___x_4228_ = 0;
v___x_4229_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4219_, v___f_4227_, v___x_4228_, v_a_4221_, v_a_4222_, v_a_4223_, v_a_4224_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4230_, lean_object* v_positions_4231_, lean_object* v_recArgInfo_4232_, lean_object* v_value_4233_, lean_object* v_FType_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4230_, v_positions_4231_, v_recArgInfo_4232_, v_value_4233_, v_FType_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
lean_dec_ref(v_a_4235_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4241_, lean_object* v_params_4242_, uint8_t v_isIndPred_4243_, lean_object* v_brecOnUniv_4244_, lean_object* v_levels_4245_, lean_object* v_idx_4246_){
_start:
{
lean_object* v_n_4247_; lean_object* v___y_4249_; 
v_n_4247_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4241_, v_idx_4246_);
if (v_isIndPred_4243_ == 0)
{
lean_object* v___x_4252_; 
v___x_4252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4252_, 0, v_brecOnUniv_4244_);
lean_ctor_set(v___x_4252_, 1, v_levels_4245_);
v___y_4249_ = v___x_4252_;
goto v___jp_4248_;
}
else
{
lean_dec(v_brecOnUniv_4244_);
v___y_4249_ = v_levels_4245_;
goto v___jp_4248_;
}
v___jp_4248_:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = l_Lean_Expr_const___override(v_n_4247_, v___y_4249_);
v___x_4251_ = l_Lean_mkAppN(v___x_4250_, v_params_4242_);
return v___x_4251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4253_, lean_object* v_params_4254_, lean_object* v_isIndPred_4255_, lean_object* v_brecOnUniv_4256_, lean_object* v_levels_4257_, lean_object* v_idx_4258_){
_start:
{
uint8_t v_isIndPred_boxed_4259_; lean_object* v_res_4260_; 
v_isIndPred_boxed_4259_ = lean_unbox(v_isIndPred_4255_);
v_res_4260_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4253_, v_params_4254_, v_isIndPred_boxed_4259_, v_brecOnUniv_4256_, v_levels_4257_, v_idx_4258_);
lean_dec(v_idx_4258_);
lean_dec_ref(v_params_4254_);
lean_dec_ref(v_toIndGroupInfo_4253_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4261_, lean_object* v_a_4262_, lean_object* v_n_4263_){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4264_ = lean_apply_1(v_brecOnCons_4261_, v_n_4263_);
v___x_4265_ = l_Lean_mkAppN(v___x_4264_, v_a_4262_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4266_, lean_object* v_a_4267_, lean_object* v_n_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4266_, v_a_4267_, v_n_4268_);
lean_dec_ref(v_a_4267_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4270_, lean_object* v_type_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l_Lean_Meta_getLevel(v_type_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4278_, lean_object* v_type_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4278_, v_type_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec_ref(v_x_4278_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4286_, size_t v_sz_4287_, size_t v_i_4288_, lean_object* v_bs_4289_){
_start:
{
uint8_t v___x_4290_; 
v___x_4290_ = lean_usize_dec_lt(v_i_4288_, v_sz_4287_);
if (v___x_4290_ == 0)
{
return v_bs_4289_;
}
else
{
lean_object* v___x_4291_; lean_object* v_v_4292_; lean_object* v___x_4293_; lean_object* v_bs_x27_4294_; lean_object* v___x_4295_; size_t v___x_4296_; size_t v___x_4297_; lean_object* v___x_4298_; 
v___x_4291_ = l_Lean_instInhabitedExpr;
v_v_4292_ = lean_array_uget(v_bs_4289_, v_i_4288_);
v___x_4293_ = lean_unsigned_to_nat(0u);
v_bs_x27_4294_ = lean_array_uset(v_bs_4289_, v_i_4288_, v___x_4293_);
v___x_4295_ = lean_array_get_borrowed(v___x_4291_, v_xs_4286_, v_v_4292_);
lean_dec(v_v_4292_);
v___x_4296_ = ((size_t)1ULL);
v___x_4297_ = lean_usize_add(v_i_4288_, v___x_4296_);
lean_inc(v___x_4295_);
v___x_4298_ = lean_array_uset(v_bs_x27_4294_, v_i_4288_, v___x_4295_);
v_i_4288_ = v___x_4297_;
v_bs_4289_ = v___x_4298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4300_, lean_object* v_sz_4301_, lean_object* v_i_4302_, lean_object* v_bs_4303_){
_start:
{
size_t v_sz_boxed_4304_; size_t v_i_boxed_4305_; lean_object* v_res_4306_; 
v_sz_boxed_4304_ = lean_unbox_usize(v_sz_4301_);
lean_dec(v_sz_4301_);
v_i_boxed_4305_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_res_4306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4300_, v_sz_boxed_4304_, v_i_boxed_4305_, v_bs_4303_);
lean_dec_ref(v_xs_4300_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4307_, lean_object* v_f_4308_, lean_object* v_as_4309_, lean_object* v_bs_4310_, lean_object* v_i_4311_, lean_object* v_cs_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4318_ = lean_array_get_size(v_as_4309_);
v___x_4319_ = lean_nat_dec_lt(v_i_4311_, v___x_4318_);
if (v___x_4319_ == 0)
{
lean_object* v___x_4320_; 
lean_dec(v_i_4311_);
lean_dec_ref(v_f_4308_);
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v_cs_4312_);
return v___x_4320_;
}
else
{
lean_object* v___x_4321_; uint8_t v___x_4322_; 
v___x_4321_ = lean_array_get_size(v_bs_4310_);
v___x_4322_ = lean_nat_dec_lt(v_i_4311_, v___x_4321_);
if (v___x_4322_ == 0)
{
lean_object* v___x_4323_; 
lean_dec(v_i_4311_);
lean_dec_ref(v_f_4308_);
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v_cs_4312_);
return v___x_4323_;
}
else
{
lean_object* v_a_4324_; lean_object* v_b_4325_; size_t v_sz_4326_; size_t v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v_a_4324_ = lean_array_fget_borrowed(v_as_4309_, v_i_4311_);
v_b_4325_ = lean_array_fget_borrowed(v_bs_4310_, v_i_4311_);
v_sz_4326_ = lean_array_size(v_b_4325_);
v___x_4327_ = ((size_t)0ULL);
lean_inc(v_b_4325_);
v___x_4328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4307_, v_sz_4326_, v___x_4327_, v_b_4325_);
lean_inc_ref(v_f_4308_);
lean_inc(v___y_4316_);
lean_inc_ref(v___y_4315_);
lean_inc(v___y_4314_);
lean_inc_ref(v___y_4313_);
lean_inc(v_a_4324_);
v___x_4329_ = lean_apply_7(v_f_4308_, v_a_4324_, v___x_4328_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, lean_box(0));
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
lean_inc(v_a_4330_);
lean_dec_ref_known(v___x_4329_, 1);
v___x_4331_ = lean_unsigned_to_nat(1u);
v___x_4332_ = lean_nat_add(v_i_4311_, v___x_4331_);
lean_dec(v_i_4311_);
v___x_4333_ = lean_array_push(v_cs_4312_, v_a_4330_);
v_i_4311_ = v___x_4332_;
v_cs_4312_ = v___x_4333_;
goto _start;
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v_cs_4312_);
lean_dec(v_i_4311_);
lean_dec_ref(v_f_4308_);
v_a_4335_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4329_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4329_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4343_, lean_object* v_f_4344_, lean_object* v_as_4345_, lean_object* v_bs_4346_, lean_object* v_i_4347_, lean_object* v_cs_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4343_, v_f_4344_, v_as_4345_, v_bs_4346_, v_i_4347_, v_cs_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec_ref(v_bs_4346_);
lean_dec_ref(v_as_4345_);
lean_dec_ref(v_xs_4343_);
return v_res_4354_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l_Array_instInhabited(lean_box(0));
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v___x_4362_; lean_object* v_toApplicative_4363_; lean_object* v_toFunctor_4364_; lean_object* v_toSeq_4365_; lean_object* v_toSeqLeft_4366_; lean_object* v_toSeqRight_4367_; lean_object* v___f_4368_; lean_object* v___f_4369_; lean_object* v___f_4370_; lean_object* v___f_4371_; lean_object* v___x_4372_; lean_object* v___f_4373_; lean_object* v___f_4374_; lean_object* v___f_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v_toApplicative_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4410_; 
v___x_4362_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4363_ = lean_ctor_get(v___x_4362_, 0);
v_toFunctor_4364_ = lean_ctor_get(v_toApplicative_4363_, 0);
v_toSeq_4365_ = lean_ctor_get(v_toApplicative_4363_, 2);
v_toSeqLeft_4366_ = lean_ctor_get(v_toApplicative_4363_, 3);
v_toSeqRight_4367_ = lean_ctor_get(v_toApplicative_4363_, 4);
v___f_4368_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4369_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4364_, 2);
v___f_4370_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4370_, 0, v_toFunctor_4364_);
v___f_4371_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4371_, 0, v_toFunctor_4364_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___f_4370_);
lean_ctor_set(v___x_4372_, 1, v___f_4371_);
lean_inc(v_toSeqRight_4367_);
v___f_4373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4373_, 0, v_toSeqRight_4367_);
lean_inc(v_toSeqLeft_4366_);
v___f_4374_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4374_, 0, v_toSeqLeft_4366_);
lean_inc(v_toSeq_4365_);
v___f_4375_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4375_, 0, v_toSeq_4365_);
v___x_4376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4372_);
lean_ctor_set(v___x_4376_, 1, v___f_4368_);
lean_ctor_set(v___x_4376_, 2, v___f_4375_);
lean_ctor_set(v___x_4376_, 3, v___f_4374_);
lean_ctor_set(v___x_4376_, 4, v___f_4373_);
v___x_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
lean_ctor_set(v___x_4377_, 1, v___f_4369_);
v___x_4378_ = l_StateRefT_x27_instMonad___redArg(v___x_4377_);
v_toApplicative_4379_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4410_ == 0)
{
lean_object* v_unused_4411_; 
v_unused_4411_ = lean_ctor_get(v___x_4378_, 1);
lean_dec(v_unused_4411_);
v___x_4381_ = v___x_4378_;
v_isShared_4382_ = v_isSharedCheck_4410_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_toApplicative_4379_);
lean_dec(v___x_4378_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4410_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v_toFunctor_4383_; lean_object* v_toSeq_4384_; lean_object* v_toSeqLeft_4385_; lean_object* v_toSeqRight_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4408_; 
v_toFunctor_4383_ = lean_ctor_get(v_toApplicative_4379_, 0);
v_toSeq_4384_ = lean_ctor_get(v_toApplicative_4379_, 2);
v_toSeqLeft_4385_ = lean_ctor_get(v_toApplicative_4379_, 3);
v_toSeqRight_4386_ = lean_ctor_get(v_toApplicative_4379_, 4);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_toApplicative_4379_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; 
v_unused_4409_ = lean_ctor_get(v_toApplicative_4379_, 1);
lean_dec(v_unused_4409_);
v___x_4388_ = v_toApplicative_4379_;
v_isShared_4389_ = v_isSharedCheck_4408_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_toSeqRight_4386_);
lean_inc(v_toSeqLeft_4385_);
lean_inc(v_toSeq_4384_);
lean_inc(v_toFunctor_4383_);
lean_dec(v_toApplicative_4379_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4408_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___f_4390_; lean_object* v___f_4391_; lean_object* v___f_4392_; lean_object* v___f_4393_; lean_object* v___x_4394_; lean_object* v___f_4395_; lean_object* v___f_4396_; lean_object* v___f_4397_; lean_object* v___x_4399_; 
v___f_4390_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4391_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4383_);
v___f_4392_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4392_, 0, v_toFunctor_4383_);
v___f_4393_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4393_, 0, v_toFunctor_4383_);
v___x_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___f_4392_);
lean_ctor_set(v___x_4394_, 1, v___f_4393_);
v___f_4395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4395_, 0, v_toSeqRight_4386_);
v___f_4396_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4396_, 0, v_toSeqLeft_4385_);
v___f_4397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4397_, 0, v_toSeq_4384_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 4, v___f_4395_);
lean_ctor_set(v___x_4388_, 3, v___f_4396_);
lean_ctor_set(v___x_4388_, 2, v___f_4397_);
lean_ctor_set(v___x_4388_, 1, v___f_4390_);
lean_ctor_set(v___x_4388_, 0, v___x_4394_);
v___x_4399_ = v___x_4388_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4394_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v___f_4390_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v___f_4397_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v___f_4396_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v___f_4395_);
v___x_4399_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
lean_object* v___x_4401_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 1, v___f_4391_);
lean_ctor_set(v___x_4381_, 0, v___x_4399_);
v___x_4401_ = v___x_4381_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4399_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v___f_4391_);
v___x_4401_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_855__overap_4404_; lean_object* v___x_4405_; 
v___x_4402_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4403_ = l_instInhabitedOfMonad___redArg(v___x_4401_, v___x_4402_);
v___x_855__overap_4404_ = lean_panic_fn_borrowed(v___x_4403_, v_msg_4356_);
lean_dec(v___x_4403_);
lean_inc(v___y_4360_);
lean_inc_ref(v___y_4359_);
lean_inc(v___y_4358_);
lean_inc_ref(v___y_4357_);
v___x_4405_ = lean_apply_5(v___x_855__overap_4404_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, lean_box(0));
return v___x_4405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
return v_res_4418_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4422_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4423_ = lean_unsigned_to_nat(2u);
v___x_4424_ = lean_unsigned_to_nat(73u);
v___x_4425_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4426_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4427_ = l_mkPanicMessageWithDecl(v___x_4426_, v___x_4425_, v___x_4424_, v___x_4423_, v___x_4422_);
return v___x_4427_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4429_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4430_ = lean_unsigned_to_nat(2u);
v___x_4431_ = lean_unsigned_to_nat(74u);
v___x_4432_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4433_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4434_ = l_mkPanicMessageWithDecl(v___x_4433_, v___x_4432_, v___x_4431_, v___x_4430_, v___x_4429_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4437_, lean_object* v_positions_4438_, lean_object* v_ys_4439_, lean_object* v_xs_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
v___x_4446_ = lean_array_get_size(v_positions_4438_);
v___x_4447_ = lean_array_get_size(v_ys_4439_);
v___x_4448_ = lean_nat_dec_eq(v___x_4446_, v___x_4447_);
if (v___x_4448_ == 0)
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_dec_ref(v_f_4437_);
v___x_4449_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4450_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4449_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4450_;
}
else
{
lean_object* v___x_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; 
v___x_4451_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4438_);
v___x_4452_ = lean_array_get_size(v_xs_4440_);
v___x_4453_ = lean_nat_dec_eq(v___x_4451_, v___x_4452_);
lean_dec(v___x_4451_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_dec_ref(v_f_4437_);
v___x_4454_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4455_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4454_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4455_;
}
else
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4456_ = lean_unsigned_to_nat(0u);
v___x_4457_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4458_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4440_, v_f_4437_, v_ys_4439_, v_positions_4438_, v___x_4456_, v___x_4457_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4459_, lean_object* v_positions_4460_, lean_object* v_ys_4461_, lean_object* v_xs_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4459_, v_positions_4460_, v_ys_4461_, v_xs_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec_ref(v_xs_4462_);
lean_dec_ref(v_ys_4461_);
lean_dec_ref(v_positions_4460_);
return v_res_4468_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = lean_unsigned_to_nat(0u);
v___x_4471_ = l_Lean_Level_ofNat(v___x_4470_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4472_, lean_object* v_positions_4473_, lean_object* v_motives_4474_, uint8_t v_isIndPred_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v_indGroupInst_4484_; lean_object* v_brecOnUniv_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; 
v___x_4481_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4482_ = lean_unsigned_to_nat(0u);
v___x_4483_ = lean_array_get_borrowed(v___x_4481_, v_recArgInfos_4472_, v___x_4482_);
v_indGroupInst_4484_ = lean_ctor_get(v___x_4483_, 4);
if (v_isIndPred_4475_ == 0)
{
lean_object* v___f_4527_; lean_object* v___x_4528_; lean_object* v_motive_4529_; lean_object* v___x_4530_; 
v___f_4527_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4528_ = l_Lean_instInhabitedExpr;
v_motive_4529_ = lean_array_get_borrowed(v___x_4528_, v_motives_4474_, v___x_4482_);
lean_inc(v_motive_4529_);
v___x_4530_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4529_, v___f_4527_, v_isIndPred_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_a_4531_);
lean_dec_ref_known(v___x_4530_, 1);
v_brecOnUniv_4486_ = v_a_4531_;
v___y_4487_ = v_a_4476_;
v___y_4488_ = v_a_4477_;
v___y_4489_ = v_a_4478_;
v___y_4490_ = v_a_4479_;
goto v___jp_4485_;
}
else
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4539_; 
v_a_4532_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4534_ = v___x_4530_;
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4530_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4537_; 
if (v_isShared_4535_ == 0)
{
v___x_4537_ = v___x_4534_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
else
{
lean_object* v___x_4540_; 
v___x_4540_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4486_ = v___x_4540_;
v___y_4487_ = v_a_4476_;
v___y_4488_ = v_a_4477_;
v___y_4489_ = v_a_4478_;
v___y_4490_ = v_a_4479_;
goto v___jp_4485_;
}
v___jp_4485_:
{
lean_object* v_toIndGroupInfo_4491_; lean_object* v_levels_4492_; lean_object* v_params_4493_; lean_object* v___x_4494_; lean_object* v_brecOnCons_4495_; lean_object* v_brecOnAux_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v_toIndGroupInfo_4491_ = lean_ctor_get(v_indGroupInst_4484_, 0);
v_levels_4492_ = lean_ctor_get(v_indGroupInst_4484_, 1);
v_params_4493_ = lean_ctor_get(v_indGroupInst_4484_, 2);
v___x_4494_ = lean_box(v_isIndPred_4475_);
lean_inc_n(v_levels_4492_, 2);
lean_inc(v_brecOnUniv_4486_);
lean_inc_ref(v_params_4493_);
lean_inc_ref(v_toIndGroupInfo_4491_);
v_brecOnCons_4495_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4495_, 0, v_toIndGroupInfo_4491_);
lean_closure_set(v_brecOnCons_4495_, 1, v_params_4493_);
lean_closure_set(v_brecOnCons_4495_, 2, v___x_4494_);
lean_closure_set(v_brecOnCons_4495_, 3, v_brecOnUniv_4486_);
lean_closure_set(v_brecOnCons_4495_, 4, v_levels_4492_);
v_brecOnAux_4496_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4491_, v_params_4493_, v_isIndPred_4475_, v_brecOnUniv_4486_, v_levels_4492_, v___x_4482_);
v___x_4497_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4491_);
v___x_4498_ = l_Lean_Meta_inferArgumentTypesN(v___x_4497_, v_brecOnAux_4496_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v___x_4500_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4501_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4500_, v_positions_4473_, v_a_4499_, v_motives_4474_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v_a_4499_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4510_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4510_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4510_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___f_4506_; lean_object* v___x_4508_; 
v___f_4506_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4506_, 0, v_brecOnCons_4495_);
lean_closure_set(v___f_4506_, 1, v_a_4502_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v___f_4506_);
v___x_4508_ = v___x_4504_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___f_4506_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_dec_ref(v_brecOnCons_4495_);
v_a_4511_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4501_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4501_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec_ref(v_brecOnCons_4495_);
v_a_4519_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4498_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4498_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4541_, lean_object* v_positions_4542_, lean_object* v_motives_4543_, lean_object* v_isIndPred_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
uint8_t v_isIndPred_boxed_4550_; lean_object* v_res_4551_; 
v_isIndPred_boxed_4550_ = lean_unbox(v_isIndPred_4544_);
v_res_4551_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4541_, v_positions_4542_, v_motives_4543_, v_isIndPred_boxed_4550_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec_ref(v_motives_4543_);
lean_dec_ref(v_positions_4542_);
lean_dec_ref(v_recArgInfos_4541_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4552_, lean_object* v_msg_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4560_, lean_object* v_msg_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4560_, v_msg_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4568_, lean_object* v_00_u03b1_4569_, lean_object* v_f_4570_, lean_object* v_positions_4571_, lean_object* v_ys_4572_, lean_object* v_xs_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4570_, v_positions_4571_, v_ys_4572_, v_xs_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4580_, lean_object* v_00_u03b1_4581_, lean_object* v_f_4582_, lean_object* v_positions_4583_, lean_object* v_ys_4584_, lean_object* v_xs_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4580_, v_00_u03b1_4581_, v_f_4582_, v_positions_4583_, v_ys_4584_, v_xs_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec_ref(v_xs_4585_);
lean_dec_ref(v_ys_4584_);
lean_dec_ref(v_positions_4583_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4592_, lean_object* v_00_u03b3_4593_, lean_object* v_xs_4594_, lean_object* v_f_4595_, lean_object* v_as_4596_, lean_object* v_bs_4597_, lean_object* v_i_4598_, lean_object* v_cs_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4594_, v_f_4595_, v_as_4596_, v_bs_4597_, v_i_4598_, v_cs_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4606_, lean_object* v_00_u03b3_4607_, lean_object* v_xs_4608_, lean_object* v_f_4609_, lean_object* v_as_4610_, lean_object* v_bs_4611_, lean_object* v_i_4612_, lean_object* v_cs_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4606_, v_00_u03b3_4607_, v_xs_4608_, v_f_4609_, v_as_4610_, v_bs_4611_, v_i_4612_, v_cs_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec_ref(v_bs_4611_);
lean_dec_ref(v_as_4610_);
lean_dec_ref(v_xs_4608_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_4620_, lean_object* v_e_4621_){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = l_Lean_indentD(v_e_4621_);
v___x_4623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4620_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_4624_, lean_object* v_x_4625_, lean_object* v_brecOnType_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
lean_object* v___x_4632_; 
v___x_4632_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4624_, v_brecOnType_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_4633_, lean_object* v_x_4634_, lean_object* v_brecOnType_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_4633_, v_x_4634_, v_brecOnType_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec_ref(v_x_4634_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4642_, lean_object* v_as_4643_, size_t v_sz_4644_, size_t v_i_4645_, lean_object* v_b_4646_){
_start:
{
uint8_t v___x_4648_; 
v___x_4648_ = lean_usize_dec_lt(v_i_4645_, v_sz_4644_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; 
lean_dec_ref(v_a_4642_);
v___x_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4649_, 0, v_b_4646_);
return v___x_4649_;
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4651_; size_t v___x_4652_; size_t v___x_4653_; 
v_a_4650_ = lean_array_uget_borrowed(v_as_4643_, v_i_4645_);
lean_inc_ref(v_a_4642_);
v___x_4651_ = lean_array_set(v_b_4646_, v_a_4650_, v_a_4642_);
v___x_4652_ = ((size_t)1ULL);
v___x_4653_ = lean_usize_add(v_i_4645_, v___x_4652_);
v_i_4645_ = v___x_4653_;
v_b_4646_ = v___x_4651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4655_, lean_object* v_as_4656_, lean_object* v_sz_4657_, lean_object* v_i_4658_, lean_object* v_b_4659_, lean_object* v___y_4660_){
_start:
{
size_t v_sz_boxed_4661_; size_t v_i_boxed_4662_; lean_object* v_res_4663_; 
v_sz_boxed_4661_ = lean_unbox_usize(v_sz_4657_);
lean_dec(v_sz_4657_);
v_i_boxed_4662_ = lean_unbox_usize(v_i_4658_);
lean_dec(v_i_4658_);
v_res_4663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4655_, v_as_4656_, v_sz_boxed_4661_, v_i_boxed_4662_, v_b_4659_);
lean_dec_ref(v_as_4656_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4664_, size_t v_sz_4665_, size_t v_i_4666_, lean_object* v_b_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
uint8_t v___x_4673_; 
v___x_4673_ = lean_usize_dec_lt(v_i_4666_, v_sz_4665_);
if (v___x_4673_ == 0)
{
lean_object* v___x_4674_; 
v___x_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4674_, 0, v_b_4667_);
return v___x_4674_;
}
else
{
lean_object* v_snd_4675_; lean_object* v_fst_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4720_; 
v_snd_4675_ = lean_ctor_get(v_b_4667_, 1);
v_fst_4676_ = lean_ctor_get(v_b_4667_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v_b_4667_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4678_ = v_b_4667_;
v_isShared_4679_ = v_isSharedCheck_4720_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_snd_4675_);
lean_inc(v_fst_4676_);
lean_dec(v_b_4667_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4720_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v_array_4680_; lean_object* v_start_4681_; lean_object* v_stop_4682_; uint8_t v___x_4683_; 
v_array_4680_ = lean_ctor_get(v_snd_4675_, 0);
v_start_4681_ = lean_ctor_get(v_snd_4675_, 1);
v_stop_4682_ = lean_ctor_get(v_snd_4675_, 2);
v___x_4683_ = lean_nat_dec_lt(v_start_4681_, v_stop_4682_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4685_; 
if (v_isShared_4679_ == 0)
{
v___x_4685_ = v___x_4678_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_fst_4676_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v_snd_4675_);
v___x_4685_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
lean_object* v___x_4686_; 
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
return v___x_4686_;
}
}
else
{
lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4716_; 
lean_inc(v_stop_4682_);
lean_inc(v_start_4681_);
lean_inc_ref(v_array_4680_);
v_isSharedCheck_4716_ = !lean_is_exclusive(v_snd_4675_);
if (v_isSharedCheck_4716_ == 0)
{
lean_object* v_unused_4717_; lean_object* v_unused_4718_; lean_object* v_unused_4719_; 
v_unused_4717_ = lean_ctor_get(v_snd_4675_, 2);
lean_dec(v_unused_4717_);
v_unused_4718_ = lean_ctor_get(v_snd_4675_, 1);
lean_dec(v_unused_4718_);
v_unused_4719_ = lean_ctor_get(v_snd_4675_, 0);
lean_dec(v_unused_4719_);
v___x_4689_ = v_snd_4675_;
v_isShared_4690_ = v_isSharedCheck_4716_;
goto v_resetjp_4688_;
}
else
{
lean_dec(v_snd_4675_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4716_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v_a_4691_; lean_object* v___x_4692_; size_t v_sz_4693_; size_t v___x_4694_; lean_object* v___x_4695_; 
v_a_4691_ = lean_array_uget_borrowed(v_as_4664_, v_i_4666_);
v___x_4692_ = lean_array_fget_borrowed(v_array_4680_, v_start_4681_);
v_sz_4693_ = lean_array_size(v___x_4692_);
v___x_4694_ = ((size_t)0ULL);
lean_inc(v_a_4691_);
v___x_4695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4691_, v___x_4692_, v_sz_4693_, v___x_4694_, v_fst_4676_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4700_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v___x_4697_ = lean_unsigned_to_nat(1u);
v___x_4698_ = lean_nat_add(v_start_4681_, v___x_4697_);
lean_dec(v_start_4681_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 1, v___x_4698_);
v___x_4700_ = v___x_4689_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_array_4680_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4707_, 2, v_stop_4682_);
v___x_4700_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
lean_object* v___x_4702_; 
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 1, v___x_4700_);
lean_ctor_set(v___x_4678_, 0, v_a_4696_);
v___x_4702_ = v___x_4678_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4696_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v___x_4700_);
v___x_4702_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
size_t v___x_4703_; size_t v___x_4704_; 
v___x_4703_ = ((size_t)1ULL);
v___x_4704_ = lean_usize_add(v_i_4666_, v___x_4703_);
v_i_4666_ = v___x_4704_;
v_b_4667_ = v___x_4702_;
goto _start;
}
}
}
else
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
lean_del_object(v___x_4689_);
lean_dec(v_stop_4682_);
lean_dec(v_start_4681_);
lean_dec_ref(v_array_4680_);
lean_del_object(v___x_4678_);
v_a_4708_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4695_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4695_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4721_, lean_object* v_sz_4722_, lean_object* v_i_4723_, lean_object* v_b_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
size_t v_sz_boxed_4730_; size_t v_i_boxed_4731_; lean_object* v_res_4732_; 
v_sz_boxed_4730_ = lean_unbox_usize(v_sz_4722_);
lean_dec(v_sz_4722_);
v_i_boxed_4731_ = lean_unbox_usize(v_i_4723_);
lean_dec(v_i_4723_);
v_res_4732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4721_, v_sz_boxed_4730_, v_i_boxed_4731_, v_b_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec_ref(v_as_4721_);
return v_res_4732_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4734_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4735_ = l_Lean_stringToMessageData(v___x_4734_);
return v___x_4735_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4736_; lean_object* v___f_4737_; 
v___x_4736_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4737_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_4737_, 0, v___x_4736_);
return v___f_4737_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4738_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4739_ = l_Lean_Expr_sort___override(v___x_4738_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4740_, lean_object* v_positions_4741_, lean_object* v_brecOnConst_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v_recArgInfo_4750_; lean_object* v_indicesPos_4751_; lean_object* v_indIdx_4752_; lean_object* v_brecOn_4753_; lean_object* v___f_4754_; uint8_t v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4748_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4749_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4750_ = lean_array_get_borrowed(v___x_4748_, v_recArgInfos_4740_, v___x_4749_);
v_indicesPos_4751_ = lean_ctor_get(v_recArgInfo_4750_, 3);
v_indIdx_4752_ = lean_ctor_get(v_recArgInfo_4750_, 5);
lean_inc(v_indIdx_4752_);
v_brecOn_4753_ = lean_apply_1(v_brecOnConst_4742_, v_indIdx_4752_);
v___f_4754_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4755_ = 0;
v___x_4756_ = lean_box(v___x_4755_);
lean_inc_ref(v_brecOn_4753_);
v___x_4757_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4757_, 0, v_brecOn_4753_);
lean_closure_set(v___x_4757_, 1, v___x_4756_);
v___x_4758_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4757_, v___f_4754_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v___x_4759_; 
lean_dec_ref_known(v___x_4758_, 1);
lean_inc(v_a_4746_);
lean_inc_ref(v_a_4745_);
lean_inc(v_a_4744_);
lean_inc_ref(v_a_4743_);
v___x_4759_ = lean_infer_type(v_brecOn_4753_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v_numTypeFormers_4761_; lean_object* v___f_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; uint8_t v___x_4767_; lean_object* v___x_4768_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_a_4760_);
lean_dec_ref_known(v___x_4759_, 1);
v_numTypeFormers_4761_ = lean_array_get_size(v_positions_4741_);
v___f_4762_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4762_, 0, v_numTypeFormers_4761_);
v___x_4763_ = lean_array_get_size(v_indicesPos_4751_);
v___x_4764_ = lean_unsigned_to_nat(1u);
v___x_4765_ = lean_nat_add(v___x_4763_, v___x_4764_);
v___x_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
v___x_4767_ = 0;
v___x_4768_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4760_, v___x_4766_, v___f_4762_, v___x_4767_, v___x_4767_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; size_t v_sz_4775_; size_t v___x_4776_; lean_object* v___x_4777_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v___x_4768_, 1);
v___x_4770_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4741_);
v___x_4771_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4772_ = lean_mk_array(v___x_4770_, v___x_4771_);
v___x_4773_ = l_Array_toSubarray___redArg(v_positions_4741_, v___x_4749_, v_numTypeFormers_4761_);
v___x_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4772_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v_sz_4775_ = lean_array_size(v_a_4769_);
v___x_4776_ = ((size_t)0ULL);
v___x_4777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4769_, v_sz_4775_, v___x_4776_, v___x_4774_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
lean_dec(v_a_4769_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4786_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4786_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4786_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v_fst_4782_; lean_object* v___x_4784_; 
v_fst_4782_ = lean_ctor_get(v_a_4778_, 0);
lean_inc(v_fst_4782_);
lean_dec(v_a_4778_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v_fst_4782_);
v___x_4784_ = v___x_4780_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_fst_4782_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
v_a_4787_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4777_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4777_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4741_);
return v___x_4768_;
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec_ref(v_positions_4741_);
v_a_4795_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4759_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4759_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec_ref(v_brecOn_4753_);
lean_dec_ref(v_positions_4741_);
v_a_4803_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4758_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4758_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4811_, lean_object* v_positions_4812_, lean_object* v_brecOnConst_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4811_, v_positions_4812_, v_brecOnConst_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_a_4815_);
lean_dec_ref(v_a_4814_);
lean_dec_ref(v_recArgInfos_4811_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4820_, lean_object* v_as_4821_, size_t v_sz_4822_, size_t v_i_4823_, lean_object* v_b_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v___x_4830_; 
v___x_4830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4820_, v_as_4821_, v_sz_4822_, v_i_4823_, v_b_4824_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4831_, lean_object* v_as_4832_, lean_object* v_sz_4833_, lean_object* v_i_4834_, lean_object* v_b_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
size_t v_sz_boxed_4841_; size_t v_i_boxed_4842_; lean_object* v_res_4843_; 
v_sz_boxed_4841_ = lean_unbox_usize(v_sz_4833_);
lean_dec(v_sz_4833_);
v_i_boxed_4842_ = lean_unbox_usize(v_i_4834_);
lean_dec(v_i_4834_);
v_res_4843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4831_, v_as_4832_, v_sz_boxed_4841_, v_i_boxed_4842_, v_b_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec_ref(v_as_4832_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
if (lean_obj_tag(v_a_4844_) == 0)
{
lean_object* v___x_4846_; 
v___x_4846_ = l_List_reverse___redArg(v_a_4845_);
return v___x_4846_;
}
else
{
lean_object* v_head_4847_; lean_object* v_tail_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4859_; 
v_head_4847_ = lean_ctor_get(v_a_4844_, 0);
v_tail_4848_ = lean_ctor_get(v_a_4844_, 1);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_a_4844_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4850_ = v_a_4844_;
v_isShared_4851_ = v_isSharedCheck_4859_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_tail_4848_);
lean_inc(v_head_4847_);
lean_dec(v_a_4844_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4859_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4856_; 
v___x_4852_ = l_Nat_reprFast(v_head_4847_);
v___x_4853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
v___x_4854_ = l_Lean_MessageData_ofFormat(v___x_4853_);
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 1, v_a_4845_);
lean_ctor_set(v___x_4850_, 0, v___x_4854_);
v___x_4856_ = v___x_4850_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_a_4845_);
v___x_4856_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
v_a_4844_ = v_tail_4848_;
v_a_4845_ = v___x_4856_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
if (lean_obj_tag(v_a_4860_) == 0)
{
lean_object* v___x_4862_; 
v___x_4862_ = l_List_reverse___redArg(v_a_4861_);
return v___x_4862_;
}
else
{
lean_object* v_head_4863_; lean_object* v_tail_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4876_; 
v_head_4863_ = lean_ctor_get(v_a_4860_, 0);
v_tail_4864_ = lean_ctor_get(v_a_4860_, 1);
v_isSharedCheck_4876_ = !lean_is_exclusive(v_a_4860_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4866_ = v_a_4860_;
v_isShared_4867_ = v_isSharedCheck_4876_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_tail_4864_);
lean_inc(v_head_4863_);
lean_dec(v_a_4860_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4876_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4868_ = lean_array_to_list(v_head_4863_);
v___x_4869_ = lean_box(0);
v___x_4870_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4868_, v___x_4869_);
v___x_4871_ = l_Lean_MessageData_ofList(v___x_4870_);
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 1, v_a_4861_);
lean_ctor_set(v___x_4866_, 0, v___x_4871_);
v___x_4873_ = v___x_4866_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v___x_4871_);
lean_ctor_set(v_reuseFailAlloc_4875_, 1, v_a_4861_);
v___x_4873_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
v_a_4860_ = v_tail_4864_;
v_a_4861_ = v___x_4873_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4877_, lean_object* v_v_4878_, lean_object* v_i_4879_){
_start:
{
lean_object* v___x_4880_; uint8_t v___x_4881_; 
v___x_4880_ = lean_array_get_size(v_xs_4877_);
v___x_4881_ = lean_nat_dec_lt(v_i_4879_, v___x_4880_);
if (v___x_4881_ == 0)
{
lean_object* v___x_4882_; 
lean_dec(v_i_4879_);
v___x_4882_ = lean_box(0);
return v___x_4882_;
}
else
{
lean_object* v___x_4883_; uint8_t v___x_4884_; 
v___x_4883_ = lean_array_fget_borrowed(v_xs_4877_, v_i_4879_);
v___x_4884_ = lean_nat_dec_eq(v___x_4883_, v_v_4878_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = lean_unsigned_to_nat(1u);
v___x_4886_ = lean_nat_add(v_i_4879_, v___x_4885_);
lean_dec(v_i_4879_);
v_i_4879_ = v___x_4886_;
goto _start;
}
else
{
lean_object* v___x_4888_; 
v___x_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4888_, 0, v_i_4879_);
return v___x_4888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4889_, lean_object* v_v_4890_, lean_object* v_i_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4889_, v_v_4890_, v_i_4891_);
lean_dec(v_v_4890_);
lean_dec_ref(v_xs_4889_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4893_, lean_object* v_v_4894_){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = lean_unsigned_to_nat(0u);
v___x_4896_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4893_, v_v_4894_, v___x_4895_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4897_, lean_object* v_v_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4897_, v_v_4898_);
lean_dec(v_v_4898_);
lean_dec_ref(v_xs_4897_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4903_, lean_object* v_as_4904_, size_t v_sz_4905_, size_t v_i_4906_, lean_object* v_b_4907_){
_start:
{
uint8_t v___x_4908_; 
v___x_4908_ = lean_usize_dec_lt(v_i_4906_, v_sz_4905_);
if (v___x_4908_ == 0)
{
lean_inc_ref(v_b_4907_);
return v_b_4907_;
}
else
{
lean_object* v___x_4909_; lean_object* v_a_4910_; lean_object* v___x_4911_; 
v___x_4909_ = lean_box(0);
v_a_4910_ = lean_array_uget_borrowed(v_as_4904_, v_i_4906_);
v___x_4911_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4910_, v_fnIdx_4903_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v___x_4912_; size_t v___x_4913_; size_t v___x_4914_; 
v___x_4912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4913_ = ((size_t)1ULL);
v___x_4914_ = lean_usize_add(v_i_4906_, v___x_4913_);
v_i_4906_ = v___x_4914_;
v_b_4907_ = v___x_4912_;
goto _start;
}
else
{
lean_object* v_val_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4927_; 
v_val_4916_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4918_ = v___x_4911_;
v_isShared_4919_ = v_isSharedCheck_4927_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_val_4916_);
lean_dec(v___x_4911_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4927_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4920_ = lean_array_get_size(v_a_4910_);
v___x_4921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
lean_ctor_set(v___x_4921_, 1, v_val_4916_);
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 0, v___x_4921_);
v___x_4923_ = v___x_4918_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4921_);
v___x_4923_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4923_);
v___x_4925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
lean_ctor_set(v___x_4925_, 1, v___x_4909_);
return v___x_4925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4928_, lean_object* v_as_4929_, lean_object* v_sz_4930_, lean_object* v_i_4931_, lean_object* v_b_4932_){
_start:
{
size_t v_sz_boxed_4933_; size_t v_i_boxed_4934_; lean_object* v_res_4935_; 
v_sz_boxed_4933_ = lean_unbox_usize(v_sz_4930_);
lean_dec(v_sz_4930_);
v_i_boxed_4934_ = lean_unbox_usize(v_i_4931_);
lean_dec(v_i_4931_);
v_res_4935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4928_, v_as_4929_, v_sz_boxed_4933_, v_i_boxed_4934_, v_b_4932_);
lean_dec_ref(v_b_4932_);
lean_dec_ref(v_as_4929_);
lean_dec(v_fnIdx_4928_);
return v_res_4935_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4937_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4938_ = l_Lean_stringToMessageData(v___x_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4939_, lean_object* v_positions_4940_, lean_object* v_fnIdx_4941_, lean_object* v_brecOnConst_4942_, lean_object* v_packedFArgs_4943_, lean_object* v_funTypes_4944_, lean_object* v_ys_4945_, lean_object* v___value_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v___x_4966_; lean_object* v_fst_4967_; lean_object* v_snd_4968_; lean_object* v___x_4969_; size_t v_sz_4970_; size_t v___x_4971_; lean_object* v___x_4972_; lean_object* v_fst_4973_; 
lean_inc_ref(v_ys_4945_);
lean_inc_ref(v_recArgInfo_4939_);
v___x_4966_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4939_, v_ys_4945_);
v_fst_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_fst_4967_);
v_snd_4968_ = lean_ctor_get(v___x_4966_, 1);
lean_inc(v_snd_4968_);
lean_dec_ref(v___x_4966_);
v___x_4969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_4970_ = lean_array_size(v_positions_4940_);
v___x_4971_ = ((size_t)0ULL);
v___x_4972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4941_, v_positions_4940_, v_sz_4970_, v___x_4971_, v___x_4969_);
v_fst_4973_ = lean_ctor_get(v___x_4972_, 0);
lean_inc(v_fst_4973_);
lean_dec_ref(v___x_4972_);
if (lean_obj_tag(v_fst_4973_) == 0)
{
lean_dec(v_snd_4968_);
lean_dec(v_fst_4967_);
lean_dec_ref(v_ys_4945_);
lean_dec_ref(v_brecOnConst_4942_);
lean_dec_ref(v_recArgInfo_4939_);
goto v___jp_4952_;
}
else
{
lean_object* v_val_4974_; 
v_val_4974_ = lean_ctor_get(v_fst_4973_, 0);
lean_inc(v_val_4974_);
lean_dec_ref_known(v_fst_4973_, 1);
if (lean_obj_tag(v_val_4974_) == 1)
{
lean_object* v_val_4975_; lean_object* v_fst_4976_; lean_object* v_snd_4977_; lean_object* v_indIdx_4978_; lean_object* v_brecOn_4979_; lean_object* v_brecOn_4980_; lean_object* v_brecOn_4981_; lean_object* v___x_4982_; 
lean_dec(v_fnIdx_4941_);
lean_dec_ref(v_positions_4940_);
v_val_4975_ = lean_ctor_get(v_val_4974_, 0);
lean_inc(v_val_4975_);
lean_dec_ref_known(v_val_4974_, 1);
v_fst_4976_ = lean_ctor_get(v_val_4975_, 0);
lean_inc(v_fst_4976_);
v_snd_4977_ = lean_ctor_get(v_val_4975_, 1);
lean_inc(v_snd_4977_);
lean_dec(v_val_4975_);
v_indIdx_4978_ = lean_ctor_get(v_recArgInfo_4939_, 5);
lean_inc(v_indIdx_4978_);
lean_dec_ref(v_recArgInfo_4939_);
v_brecOn_4979_ = lean_apply_1(v_brecOnConst_4942_, v_indIdx_4978_);
v_brecOn_4980_ = l_Lean_mkAppN(v_brecOn_4979_, v_fst_4967_);
lean_dec(v_fst_4967_);
v_brecOn_4981_ = l_Lean_mkAppN(v_brecOn_4980_, v_packedFArgs_4943_);
v___x_4982_ = l_Lean_Meta_PProdN_projM(v_fst_4976_, v_snd_4977_, v_brecOn_4981_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
lean_dec(v_snd_4977_);
lean_dec(v_fst_4976_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; uint8_t v___x_4986_; lean_object* v___x_4987_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___x_4982_, 1);
v___x_4984_ = l_Lean_mkAppN(v_a_4983_, v_snd_4968_);
lean_dec(v_snd_4968_);
v___x_4985_ = 1;
v___x_4986_ = 1;
v___x_4987_ = l_Lean_Meta_mkLetFVars(v_funTypes_4944_, v___x_4984_, v___x_4985_, v___x_4985_, v___x_4986_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v_a_4988_; uint8_t v___x_4989_; lean_object* v___x_4990_; 
v_a_4988_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4988_);
lean_dec_ref_known(v___x_4987_, 1);
v___x_4989_ = 0;
v___x_4990_ = l_Lean_Meta_mkLambdaFVars(v_ys_4945_, v_a_4988_, v___x_4989_, v___x_4985_, v___x_4989_, v___x_4985_, v___x_4986_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
lean_dec_ref(v_ys_4945_);
return v___x_4990_;
}
else
{
lean_dec_ref(v_ys_4945_);
return v___x_4987_;
}
}
else
{
lean_dec(v_snd_4968_);
lean_dec_ref(v_ys_4945_);
return v___x_4982_;
}
}
else
{
lean_dec(v_val_4974_);
lean_dec(v_snd_4968_);
lean_dec(v_fst_4967_);
lean_dec_ref(v_ys_4945_);
lean_dec_ref(v_brecOnConst_4942_);
lean_dec_ref(v_recArgInfo_4939_);
goto v___jp_4952_;
}
}
v___jp_4952_:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4953_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_4954_ = l_Nat_reprFast(v_fnIdx_4941_);
v___x_4955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
v___x_4956_ = l_Lean_MessageData_ofFormat(v___x_4955_);
v___x_4957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4953_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_4959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4957_);
lean_ctor_set(v___x_4959_, 1, v___x_4958_);
v___x_4960_ = lean_array_to_list(v_positions_4940_);
v___x_4961_ = lean_box(0);
v___x_4962_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_4960_, v___x_4961_);
v___x_4963_ = l_Lean_MessageData_ofList(v___x_4962_);
v___x_4964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4959_);
lean_ctor_set(v___x_4964_, 1, v___x_4963_);
v___x_4965_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4964_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
return v___x_4965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_4991_, lean_object* v_positions_4992_, lean_object* v_fnIdx_4993_, lean_object* v_brecOnConst_4994_, lean_object* v_packedFArgs_4995_, lean_object* v_funTypes_4996_, lean_object* v_ys_4997_, lean_object* v___value_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_4991_, v_positions_4992_, v_fnIdx_4993_, v_brecOnConst_4994_, v_packedFArgs_4995_, v_funTypes_4996_, v_ys_4997_, v___value_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___y_5002_);
lean_dec_ref(v___y_5001_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
lean_dec_ref(v___value_4998_);
lean_dec_ref(v_funTypes_4996_);
lean_dec_ref(v_packedFArgs_4995_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5005_, lean_object* v_fnIdx_5006_, lean_object* v_brecOnConst_5007_, lean_object* v_packedFArgs_5008_, lean_object* v_funTypes_5009_, lean_object* v_recArgInfo_5010_, lean_object* v_value_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v___f_5017_; uint8_t v___x_5018_; lean_object* v___x_5019_; 
v___f_5017_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5017_, 0, v_recArgInfo_5010_);
lean_closure_set(v___f_5017_, 1, v_positions_5005_);
lean_closure_set(v___f_5017_, 2, v_fnIdx_5006_);
lean_closure_set(v___f_5017_, 3, v_brecOnConst_5007_);
lean_closure_set(v___f_5017_, 4, v_packedFArgs_5008_);
lean_closure_set(v___f_5017_, 5, v_funTypes_5009_);
v___x_5018_ = 0;
v___x_5019_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5011_, v___f_5017_, v___x_5018_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5020_, lean_object* v_fnIdx_5021_, lean_object* v_brecOnConst_5022_, lean_object* v_packedFArgs_5023_, lean_object* v_funTypes_5024_, lean_object* v_recArgInfo_5025_, lean_object* v_value_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5020_, v_fnIdx_5021_, v_brecOnConst_5022_, v_packedFArgs_5023_, v_funTypes_5024_, v_recArgInfo_5025_, v_value_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
return v_res_5032_;
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
