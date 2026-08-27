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
lean_object* v___x_836_; lean_object* v___f_837_; size_t v_sz_838_; size_t v___x_839_; lean_object* v___x_7103__overap_840_; lean_object* v___x_841_; 
v___x_836_ = lean_array_fget_borrowed(v_array_824_, v_start_825_);
lean_inc(v___x_836_);
v___f_837_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_837_, 0, v___x_836_);
v_sz_838_ = lean_array_size(v_a_811_);
v___x_839_ = ((size_t)0ULL);
v___x_7103__overap_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_810_, v_a_811_, v___f_837_, v_sz_838_, v___x_839_, v_fst_820_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
v___x_841_ = lean_apply_5(v___x_7103__overap_840_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, lean_box(0));
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_893_, lean_object* v___x_894_, lean_object* v_positions_895_, lean_object* v_a_896_, lean_object* v___f_897_, lean_object* v___x_898_, lean_object* v___x_899_, lean_object* v_k_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v_toMonadRef_903_, lean_object* v___x_904_, lean_object* v_Cs_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_7130__overap_912_; lean_object* v___x_913_; 
v___x_911_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_905_);
lean_inc_ref(v___x_893_);
v___x_7130__overap_912_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_893_, v___x_894_, v___x_911_, v_positions_895_, v_a_896_, v_Cs_905_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
v___x_913_ = lean_apply_5(v___x_7130__overap_912_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, lean_box(0));
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
v___x_915_ = lean_apply_5(v___f_897_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, lean_box(0));
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; uint8_t v___x_957_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = l_Lean_mkAppN(v___x_898_, v_a_914_);
lean_dec(v_a_914_);
v___x_918_ = l_Subarray_copy___redArg(v___x_899_);
v___x_919_ = l_Lean_mkAppN(v___x_917_, v___x_918_);
lean_dec_ref(v___x_918_);
v___x_957_ = lean_unbox(v_a_916_);
lean_dec(v_a_916_);
if (v___x_957_ == 0)
{
v___y_921_ = v___y_906_;
v___y_922_ = v___y_907_;
v___y_923_ = v___y_908_;
v___y_924_ = v___y_909_;
goto v___jp_920_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_7180__overap_969_; lean_object* v___x_970_; 
v___x_958_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_Cs_905_);
v___x_959_ = lean_array_to_list(v_Cs_905_);
v___x_960_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_961_ = lean_box(0);
v___x_962_ = l_List_mapTR_loop___redArg(v___x_960_, v___x_959_, v___x_961_);
v___x_963_ = l_Lean_MessageData_ofList(v___x_962_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_958_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
lean_inc_ref(v___x_919_);
v___x_967_ = l_Lean_indentExpr(v___x_919_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
lean_inc(v___x_901_);
lean_inc_ref(v___x_904_);
lean_inc_ref(v_toMonadRef_903_);
lean_inc_ref(v___x_902_);
lean_inc_ref(v___x_893_);
v___x_7180__overap_969_ = l_Lean_addTrace___redArg(v___x_893_, v___x_902_, v_toMonadRef_903_, v___x_904_, v___x_901_, v___x_968_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
v___x_970_ = lean_apply_5(v___x_7180__overap_969_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, lean_box(0));
if (lean_obj_tag(v___x_970_) == 0)
{
lean_dec_ref_known(v___x_970_, 1);
v___y_921_ = v___y_906_;
v___y_922_ = v___y_907_;
v___y_923_ = v___y_908_;
v___y_924_ = v___y_909_;
goto v___jp_920_;
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v___x_919_);
lean_dec_ref(v_Cs_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v_toMonadRef_903_);
lean_dec_ref(v___x_902_);
lean_dec(v___x_901_);
lean_dec_ref(v_k_900_);
lean_dec_ref(v___x_893_);
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
v___jp_920_:
{
lean_object* v___x_925_; 
lean_inc_ref(v___x_919_);
v___x_925_ = l_Lean_Meta_isTypeCorrect(v___x_919_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; uint8_t v___x_927_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = lean_unbox(v_a_926_);
lean_dec(v_a_926_);
if (v___x_927_ == 0)
{
lean_object* v_options_928_; uint8_t v_hasTrace_929_; 
v_options_928_ = lean_ctor_get(v___y_923_, 2);
v_hasTrace_929_ = lean_ctor_get_uint8(v_options_928_, sizeof(void*)*1);
if (v_hasTrace_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v_toMonadRef_903_);
lean_dec_ref(v___x_902_);
lean_dec(v___x_901_);
lean_dec_ref(v___x_893_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
v___x_930_ = lean_apply_7(v_k_900_, v_Cs_905_, v___x_919_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, lean_box(0));
return v___x_930_;
}
else
{
lean_object* v_inheritedTraceOptions_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_inheritedTraceOptions_931_ = lean_ctor_get(v___y_923_, 13);
v___x_932_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_901_);
v___x_933_ = l_Lean_Name_append(v___x_932_, v___x_901_);
v___x_934_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_931_, v_options_928_, v___x_933_);
lean_dec(v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v_toMonadRef_903_);
lean_dec_ref(v___x_902_);
lean_dec(v___x_901_);
lean_dec_ref(v___x_893_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
v___x_935_ = lean_apply_7(v_k_900_, v_Cs_905_, v___x_919_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, lean_box(0));
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_7156__overap_937_; lean_object* v___x_938_; 
v___x_936_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
v___x_7156__overap_937_ = l_Lean_addTrace___redArg(v___x_893_, v___x_902_, v_toMonadRef_903_, v___x_904_, v___x_901_, v___x_936_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
v___x_938_ = lean_apply_5(v___x_7156__overap_937_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, lean_box(0));
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; 
lean_dec_ref_known(v___x_938_, 1);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
v___x_939_ = lean_apply_7(v_k_900_, v_Cs_905_, v___x_919_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, lean_box(0));
return v___x_939_;
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v___x_919_);
lean_dec_ref(v_Cs_905_);
lean_dec_ref(v_k_900_);
v_a_940_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_938_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
else
{
lean_object* v___x_948_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v_toMonadRef_903_);
lean_dec_ref(v___x_902_);
lean_dec(v___x_901_);
lean_dec_ref(v___x_893_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
v___x_948_ = lean_apply_7(v_k_900_, v_Cs_905_, v___x_919_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, lean_box(0));
return v___x_948_;
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v___x_919_);
lean_dec_ref(v_Cs_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v_toMonadRef_903_);
lean_dec_ref(v___x_902_);
lean_dec(v___x_901_);
lean_dec_ref(v_k_900_);
lean_dec_ref(v___x_893_);
v_a_949_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_925_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_925_);
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
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_a_914_);
lean_dec_ref(v_Cs_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v_toMonadRef_903_);
lean_dec_ref(v___x_902_);
lean_dec(v___x_901_);
lean_dec_ref(v_k_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v___x_893_);
v_a_979_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_915_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_915_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v_Cs_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v_toMonadRef_903_);
lean_dec_ref(v___x_902_);
lean_dec(v___x_901_);
lean_dec_ref(v_k_900_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v___f_897_);
lean_dec_ref(v___x_893_);
v_a_987_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_913_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_913_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_995_ = _args[0];
lean_object* v___x_996_ = _args[1];
lean_object* v_positions_997_ = _args[2];
lean_object* v_a_998_ = _args[3];
lean_object* v___f_999_ = _args[4];
lean_object* v___x_1000_ = _args[5];
lean_object* v___x_1001_ = _args[6];
lean_object* v_k_1002_ = _args[7];
lean_object* v___x_1003_ = _args[8];
lean_object* v___x_1004_ = _args[9];
lean_object* v_toMonadRef_1005_ = _args[10];
lean_object* v___x_1006_ = _args[11];
lean_object* v_Cs_1007_ = _args[12];
lean_object* v___y_1008_ = _args[13];
lean_object* v___y_1009_ = _args[14];
lean_object* v___y_1010_ = _args[15];
lean_object* v___y_1011_ = _args[16];
lean_object* v___y_1012_ = _args[17];
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_995_, v___x_996_, v_positions_997_, v_a_998_, v___f_999_, v___x_1000_, v___x_1001_, v_k_1002_, v___x_1003_, v___x_1004_, v_toMonadRef_1005_, v___x_1006_, v_Cs_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1013_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_unsigned_to_nat(37u);
v___x_1015_ = l_Lean_Level_ofNat(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1017_ = l_Lean_Expr_sort___override(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1024_, lean_object* v___x_1025_, lean_object* v___f_1026_, lean_object* v___f_1027_, lean_object* v___x_1028_, lean_object* v_numTypeFormers_1029_, lean_object* v___f_1030_, lean_object* v___x_1031_, lean_object* v_k_1032_, lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v_toMonadRef_1035_, lean_object* v___x_1036_, lean_object* v_numIndParams_1037_, lean_object* v_a_1038_, lean_object* v_f_1039_, lean_object* v_args_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = lean_nat_add(v_numIndParams_1037_, v_numTypeFormers_1029_);
v___x_1173_ = lean_array_get_size(v_args_1040_);
v___x_1174_ = lean_nat_dec_lt(v___x_1172_, v___x_1173_);
lean_dec(v___x_1172_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_dec_ref(v_args_1040_);
lean_dec_ref(v_f_1039_);
lean_dec(v_numIndParams_1037_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v___x_1031_);
lean_dec(v_numTypeFormers_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v_positions_1024_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
v___x_1175_ = lean_apply_5(v___f_1030_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; uint8_t v___x_1177_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = lean_unbox(v_a_1176_);
lean_dec(v_a_1176_);
if (v___x_1177_ == 0)
{
lean_dec_ref(v_a_1038_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec_ref(v___x_1025_);
v___y_1159_ = v___y_1041_;
v___y_1160_ = v___y_1042_;
v___y_1161_ = v___y_1043_;
v___y_1162_ = v___y_1044_;
goto v___jp_1158_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_7312__overap_1181_; lean_object* v___x_1182_; 
v___x_1178_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1179_ = l_Lean_indentExpr(v_a_1038_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_7312__overap_1181_ = l_Lean_addTrace___redArg(v___x_1025_, v___x_1034_, v_toMonadRef_1035_, v___x_1036_, v___x_1033_, v___x_1180_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
v___x_1182_ = lean_apply_5(v___x_7312__overap_1181_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_dec_ref_known(v___x_1182_, 1);
v___y_1159_ = v___y_1041_;
v___y_1160_ = v___y_1042_;
v___y_1161_ = v___y_1043_;
v___y_1162_ = v___y_1044_;
goto v___jp_1158_;
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_a_1038_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec_ref(v___x_1025_);
v_a_1191_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1175_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1175_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_dec_ref(v_a_1038_);
v___y_1147_ = v___y_1041_;
v___y_1148_ = v___y_1042_;
v___y_1149_ = v___y_1043_;
v___y_1150_ = v___y_1044_;
goto v___jp_1146_;
}
v___jp_1046_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_7225__overap_1062_; lean_object* v___x_1063_; 
v___x_1055_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1056_ = lean_mk_array(v___y_1047_, v___x_1055_);
v___x_1057_ = lean_array_get_size(v___y_1048_);
v___x_1058_ = l_Array_toSubarray___redArg(v___y_1048_, v___y_1050_, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1056_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v_sz_1060_ = lean_array_size(v_positions_1024_);
v___x_1061_ = ((size_t)0ULL);
lean_inc_ref(v___x_1025_);
v___x_7225__overap_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1025_, v_positions_1024_, v___f_1026_, v_sz_1060_, v___x_1061_, v___x_1059_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
v___x_1063_ = lean_apply_5(v___x_7225__overap_1062_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, lean_box(0));
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v_fst_1065_; size_t v_sz_1066_; lean_object* v___x_7228__overap_1067_; lean_object* v___x_1068_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v_fst_1065_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_fst_1065_);
lean_dec(v_a_1064_);
v_sz_1066_ = lean_array_size(v_fst_1065_);
lean_inc_ref(v___x_1025_);
v___x_7228__overap_1067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1025_, v___f_1027_, v_sz_1066_, v___x_1061_, v_fst_1065_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
v___x_1068_ = lean_apply_5(v___x_7228__overap_1067_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, lean_box(0));
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; uint8_t v___x_1070_; lean_object* v___x_7232__overap_1071_; lean_object* v___x_1072_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = 0;
v___x_7232__overap_1071_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1028_, v___x_1025_, v_a_1069_, v___y_1049_, v___x_1070_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
v___x_1072_ = lean_apply_5(v___x_7232__overap_1071_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, lean_box(0));
return v___x_1072_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v___y_1049_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___x_1025_);
v_a_1073_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1068_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1068_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v___y_1049_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___x_1025_);
v_a_1081_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1063_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1063_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
v___jp_1089_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = l_Subarray_copy___redArg(v___y_1095_);
v___x_1098_ = l_Lean_mkAppN(v_f_1039_, v___x_1097_);
lean_dec_ref(v___x_1097_);
lean_inc_ref(v___x_1098_);
v___x_1099_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1029_, v___x_1098_, v___y_1091_, v___y_1092_, v___y_1090_, v___y_1093_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
lean_inc_ref(v___f_1030_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
v___x_1101_ = lean_apply_5(v___f_1030_, v___y_1091_, v___y_1092_, v___y_1090_, v___y_1093_, lean_box(0));
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v_lower_1103_; lean_object* v_upper_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1129_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v_lower_1103_ = lean_ctor_get(v___y_1096_, 0);
v_upper_1104_ = lean_ctor_get(v___y_1096_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___y_1096_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1106_ = v___y_1096_;
v_isShared_1107_ = v_isSharedCheck_1129_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_upper_1104_);
lean_inc(v_lower_1103_);
lean_dec(v___y_1096_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1129_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1108_ = l_Array_toSubarray___redArg(v_args_1040_, v_lower_1103_, v_upper_1104_);
lean_inc_ref(v___x_1036_);
lean_inc_ref(v_toMonadRef_1035_);
lean_inc_ref(v___x_1034_);
lean_inc(v___x_1033_);
lean_inc(v_a_1100_);
lean_inc_ref(v_positions_1024_);
lean_inc_ref(v___x_1025_);
v___f_1109_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1109_, 0, v___x_1025_);
lean_closure_set(v___f_1109_, 1, v___x_1031_);
lean_closure_set(v___f_1109_, 2, v_positions_1024_);
lean_closure_set(v___f_1109_, 3, v_a_1100_);
lean_closure_set(v___f_1109_, 4, v___f_1030_);
lean_closure_set(v___f_1109_, 5, v___x_1098_);
lean_closure_set(v___f_1109_, 6, v___x_1108_);
lean_closure_set(v___f_1109_, 7, v_k_1032_);
lean_closure_set(v___f_1109_, 8, v___x_1033_);
lean_closure_set(v___f_1109_, 9, v___x_1034_);
lean_closure_set(v___f_1109_, 10, v_toMonadRef_1035_);
lean_closure_set(v___f_1109_, 11, v___x_1036_);
v___x_1110_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1024_);
v___x_1111_ = lean_unbox(v_a_1102_);
lean_dec(v_a_1102_);
if (v___x_1111_ == 0)
{
lean_del_object(v___x_1106_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
v___y_1047_ = v___x_1110_;
v___y_1048_ = v_a_1100_;
v___y_1049_ = v___f_1109_;
v___y_1050_ = v___y_1094_;
v___y_1051_ = v___y_1091_;
v___y_1052_ = v___y_1092_;
v___y_1053_ = v___y_1090_;
v___y_1054_ = v___y_1093_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1112_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1110_);
v___x_1113_ = l_Nat_reprFast(v___x_1110_);
v___x_1114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
v___x_1115_ = l_Lean_MessageData_ofFormat(v___x_1114_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 7);
lean_ctor_set(v___x_1106_, 1, v___x_1115_);
lean_ctor_set(v___x_1106_, 0, v___x_1112_);
v___x_1117_ = v___x_1106_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_7265__overap_1118_; lean_object* v___x_1119_; 
lean_inc_ref(v___x_1025_);
v___x_7265__overap_1118_ = l_Lean_addTrace___redArg(v___x_1025_, v___x_1034_, v_toMonadRef_1035_, v___x_1036_, v___x_1033_, v___x_1117_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
v___x_1119_ = lean_apply_5(v___x_7265__overap_1118_, v___y_1091_, v___y_1092_, v___y_1090_, v___y_1093_, lean_box(0));
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_dec_ref_known(v___x_1119_, 1);
v___y_1047_ = v___x_1110_;
v___y_1048_ = v_a_1100_;
v___y_1049_ = v___f_1109_;
v___y_1050_ = v___y_1094_;
v___y_1051_ = v___y_1091_;
v___y_1052_ = v___y_1092_;
v___y_1053_ = v___y_1090_;
v___y_1054_ = v___y_1093_;
goto v___jp_1046_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v___x_1110_);
lean_dec_ref(v___f_1109_);
lean_dec(v_a_1100_);
lean_dec(v___y_1094_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_positions_1024_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
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
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_a_1100_);
lean_dec_ref(v___x_1098_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1094_);
lean_dec_ref(v_args_1040_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v___f_1030_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_positions_1024_);
v_a_1130_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1101_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1101_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v___x_1098_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1094_);
lean_dec_ref(v_args_1040_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v___f_1030_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_positions_1024_);
v_a_1138_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1099_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1099_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
v___jp_1146_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1037_);
lean_inc_ref(v_args_1040_);
v___x_1152_ = l_Array_toSubarray___redArg(v_args_1040_, v___x_1151_, v_numIndParams_1037_);
v___x_1153_ = lean_nat_add(v_numIndParams_1037_, v_numTypeFormers_1029_);
lean_dec(v_numIndParams_1037_);
v___x_1154_ = lean_array_get_size(v_args_1040_);
v___x_1155_ = lean_nat_dec_le(v___x_1153_, v___x_1151_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1153_);
lean_ctor_set(v___x_1156_, 1, v___x_1154_);
v___y_1090_ = v___y_1149_;
v___y_1091_ = v___y_1147_;
v___y_1092_ = v___y_1148_;
v___y_1093_ = v___y_1150_;
v___y_1094_ = v___x_1151_;
v___y_1095_ = v___x_1152_;
v___y_1096_ = v___x_1156_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v___x_1153_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1151_);
lean_ctor_set(v___x_1157_, 1, v___x_1154_);
v___y_1090_ = v___y_1149_;
v___y_1091_ = v___y_1147_;
v___y_1092_ = v___y_1148_;
v___y_1093_ = v___y_1150_;
v___y_1094_ = v___x_1151_;
v___y_1095_ = v___x_1152_;
v___y_1096_ = v___x_1157_;
goto v___jp_1089_;
}
}
v___jp_1158_:
{
lean_object* v___x_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v___x_1163_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1199_ = _args[0];
lean_object* v___x_1200_ = _args[1];
lean_object* v___f_1201_ = _args[2];
lean_object* v___f_1202_ = _args[3];
lean_object* v___x_1203_ = _args[4];
lean_object* v_numTypeFormers_1204_ = _args[5];
lean_object* v___f_1205_ = _args[6];
lean_object* v___x_1206_ = _args[7];
lean_object* v_k_1207_ = _args[8];
lean_object* v___x_1208_ = _args[9];
lean_object* v___x_1209_ = _args[10];
lean_object* v_toMonadRef_1210_ = _args[11];
lean_object* v___x_1211_ = _args[12];
lean_object* v_numIndParams_1212_ = _args[13];
lean_object* v_a_1213_ = _args[14];
lean_object* v_f_1214_ = _args[15];
lean_object* v_args_1215_ = _args[16];
lean_object* v___y_1216_ = _args[17];
lean_object* v___y_1217_ = _args[18];
lean_object* v___y_1218_ = _args[19];
lean_object* v___y_1219_ = _args[20];
lean_object* v___y_1220_ = _args[21];
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1199_, v___x_1200_, v___f_1201_, v___f_1202_, v___x_1203_, v_numTypeFormers_1204_, v___f_1205_, v___x_1206_, v_k_1207_, v___x_1208_, v___x_1209_, v_toMonadRef_1210_, v___x_1211_, v_numIndParams_1212_, v_a_1213_, v_f_1214_, v_args_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1221_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_instMonadEIO(lean_box(0));
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1224_ = l_StateRefT_x27_instMonad___redArg(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1232_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1233_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1232_, v___x_1231_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___f_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1235_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1236_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1235_, v___x_1234_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1240_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1241_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
v___x_1242_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1241_, v___x_1240_, v___x_1239_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1244_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1245_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1246_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1245_, v___f_1244_, v___x_1243_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16));
v___x_1252_ = l_Lean_stringToMessageData(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1253_, lean_object* v_numIndParams_1254_, lean_object* v_positions_1255_, lean_object* v_k_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v_toApplicative_1263_; lean_object* v_toFunctor_1264_; lean_object* v_toSeq_1265_; lean_object* v_toSeqLeft_1266_; lean_object* v_toSeqRight_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_toApplicative_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1401_; 
v___x_1262_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1263_ = lean_ctor_get(v___x_1262_, 0);
v_toFunctor_1264_ = lean_ctor_get(v_toApplicative_1263_, 0);
v_toSeq_1265_ = lean_ctor_get(v_toApplicative_1263_, 2);
v_toSeqLeft_1266_ = lean_ctor_get(v_toApplicative_1263_, 3);
v_toSeqRight_1267_ = lean_ctor_get(v_toApplicative_1263_, 4);
v___f_1268_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1269_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1264_, 2);
v___f_1270_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1270_, 0, v_toFunctor_1264_);
v___f_1271_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1271_, 0, v_toFunctor_1264_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___f_1270_);
lean_ctor_set(v___x_1272_, 1, v___f_1271_);
lean_inc(v_toSeqRight_1267_);
v___f_1273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1273_, 0, v_toSeqRight_1267_);
lean_inc(v_toSeqLeft_1266_);
v___f_1274_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1274_, 0, v_toSeqLeft_1266_);
lean_inc(v_toSeq_1265_);
v___f_1275_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1275_, 0, v_toSeq_1265_);
v___x_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1272_);
lean_ctor_set(v___x_1276_, 1, v___f_1268_);
lean_ctor_set(v___x_1276_, 2, v___f_1275_);
lean_ctor_set(v___x_1276_, 3, v___f_1274_);
lean_ctor_set(v___x_1276_, 4, v___f_1273_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v___f_1269_);
v___x_1278_ = l_StateRefT_x27_instMonad___redArg(v___x_1277_);
v_toApplicative_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1278_, 1);
lean_dec(v_unused_1402_);
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1401_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_toApplicative_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1401_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_toFunctor_1283_; lean_object* v_toSeq_1284_; lean_object* v_toSeqLeft_1285_; lean_object* v_toSeqRight_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1399_; 
v_toFunctor_1283_ = lean_ctor_get(v_toApplicative_1279_, 0);
v_toSeq_1284_ = lean_ctor_get(v_toApplicative_1279_, 2);
v_toSeqLeft_1285_ = lean_ctor_get(v_toApplicative_1279_, 3);
v_toSeqRight_1286_ = lean_ctor_get(v_toApplicative_1279_, 4);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_toApplicative_1279_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_toApplicative_1279_, 1);
lean_dec(v_unused_1400_);
v___x_1288_ = v_toApplicative_1279_;
v_isShared_1289_ = v_isSharedCheck_1399_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_toSeqRight_1286_);
lean_inc(v_toSeqLeft_1285_);
lean_inc(v_toSeq_1284_);
lean_inc(v_toFunctor_1283_);
lean_dec(v_toApplicative_1279_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1399_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___f_1297_; lean_object* v___x_1299_; 
v___f_1290_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1291_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1283_);
v___f_1292_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1292_, 0, v_toFunctor_1283_);
v___f_1293_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1293_, 0, v_toFunctor_1283_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___f_1292_);
lean_ctor_set(v___x_1294_, 1, v___f_1293_);
v___f_1295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1295_, 0, v_toSeqRight_1286_);
v___f_1296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1296_, 0, v_toSeqLeft_1285_);
v___f_1297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1297_, 0, v_toSeq_1284_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 4, v___f_1295_);
lean_ctor_set(v___x_1288_, 3, v___f_1296_);
lean_ctor_set(v___x_1288_, 2, v___f_1297_);
lean_ctor_set(v___x_1288_, 1, v___f_1290_);
lean_ctor_set(v___x_1288_, 0, v___x_1294_);
v___x_1299_ = v___x_1288_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___f_1290_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v___f_1297_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v___f_1296_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v___f_1295_);
v___x_1299_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___f_1291_);
lean_ctor_set(v___x_1281_, 0, v___x_1299_);
v___x_1301_ = v___x_1281_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___f_1291_);
v___x_1301_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; lean_object* v_toApplicative_1303_; lean_object* v_toFunctor_1304_; lean_object* v_toSeq_1305_; lean_object* v_toSeqLeft_1306_; lean_object* v_toSeqRight_1307_; lean_object* v___f_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; lean_object* v___f_1312_; lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_toMonadRef_1320_; lean_object* v___x_1321_; 
v___x_1302_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1303_ = lean_ctor_get(v___x_1262_, 0);
v_toFunctor_1304_ = lean_ctor_get(v_toApplicative_1303_, 0);
v_toSeq_1305_ = lean_ctor_get(v_toApplicative_1303_, 2);
v_toSeqLeft_1306_ = lean_ctor_get(v_toApplicative_1303_, 3);
v_toSeqRight_1307_ = lean_ctor_get(v_toApplicative_1303_, 4);
lean_inc_ref_n(v_toFunctor_1304_, 2);
v___f_1308_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1308_, 0, v_toFunctor_1304_);
v___f_1309_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1309_, 0, v_toFunctor_1304_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___f_1308_);
lean_ctor_set(v___x_1310_, 1, v___f_1309_);
lean_inc(v_toSeqRight_1307_);
v___f_1311_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1311_, 0, v_toSeqRight_1307_);
lean_inc(v_toSeqLeft_1306_);
v___f_1312_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1312_, 0, v_toSeqLeft_1306_);
lean_inc(v_toSeq_1305_);
v___f_1313_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1313_, 0, v_toSeq_1305_);
v___x_1314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1310_);
lean_ctor_set(v___x_1314_, 1, v___f_1268_);
lean_ctor_set(v___x_1314_, 2, v___f_1313_);
lean_ctor_set(v___x_1314_, 3, v___f_1312_);
lean_ctor_set(v___x_1314_, 4, v___f_1311_);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___f_1269_);
v___x_1316_ = l_StateRefT_x27_instMonad___redArg(v___x_1315_);
v___x_1317_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1317_, 0, lean_box(0));
lean_closure_set(v___x_1317_, 1, lean_box(0));
lean_closure_set(v___x_1317_, 2, v___x_1316_);
v___x_1318_ = l_instMonadControlTOfPure___redArg(v___x_1317_);
v___x_1319_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1260_);
lean_inc_ref(v_a_1259_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc_ref(v_below_1253_);
v___x_1321_ = lean_infer_type(v_below_1253_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; lean_object* v___x_1325_; lean_object* v_a_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_numTypeFormers_1331_; lean_object* v___f_1332_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; uint8_t v___x_1375_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_n(v_a_1322_, 2);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1324_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
v___x_1325_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1323_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v___f_1327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15));
lean_inc_ref_n(v___x_1301_, 2);
v___f_1328_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed), 9, 1);
lean_closure_set(v___f_1328_, 0, v___x_1301_);
v___x_1329_ = l_Lean_instInhabitedExpr;
v___x_1330_ = l_Lean_Meta_instAddMessageContextMetaM;
v_numTypeFormers_1331_ = lean_array_get_size(v_positions_1255_);
lean_inc_ref(v_toMonadRef_1320_);
v___f_1332_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1332_, 0, v_positions_1255_);
lean_closure_set(v___f_1332_, 1, v___x_1301_);
lean_closure_set(v___f_1332_, 2, v___f_1328_);
lean_closure_set(v___f_1332_, 3, v___f_1327_);
lean_closure_set(v___f_1332_, 4, v___x_1318_);
lean_closure_set(v___f_1332_, 5, v_numTypeFormers_1331_);
lean_closure_set(v___f_1332_, 6, v___f_1324_);
lean_closure_set(v___f_1332_, 7, v___x_1329_);
lean_closure_set(v___f_1332_, 8, v_k_1256_);
lean_closure_set(v___f_1332_, 9, v___x_1323_);
lean_closure_set(v___f_1332_, 10, v___x_1302_);
lean_closure_set(v___f_1332_, 11, v_toMonadRef_1320_);
lean_closure_set(v___f_1332_, 12, v___x_1330_);
lean_closure_set(v___f_1332_, 13, v_numIndParams_1254_);
lean_closure_set(v___f_1332_, 14, v_a_1322_);
v___x_1375_ = lean_unbox(v_a_1326_);
lean_dec(v_a_1326_);
if (v___x_1375_ == 0)
{
v___y_1346_ = v_a_1257_;
v___y_1347_ = v_a_1258_;
v___y_1348_ = v_a_1259_;
v___y_1349_ = v_a_1260_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_6848__overap_1379_; lean_object* v___x_1380_; 
v___x_1376_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17);
lean_inc(v_a_1322_);
v___x_1377_ = l_Lean_MessageData_ofExpr(v_a_1322_);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
lean_inc_ref(v_toMonadRef_1320_);
lean_inc_ref(v___x_1301_);
v___x_6848__overap_1379_ = l_Lean_addTrace___redArg(v___x_1301_, v___x_1302_, v_toMonadRef_1320_, v___x_1330_, v___x_1323_, v___x_1378_);
lean_inc(v_a_1260_);
lean_inc_ref(v_a_1259_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
v___x_1380_ = lean_apply_5(v___x_6848__overap_1379_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, lean_box(0));
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_dec_ref_known(v___x_1380_, 1);
v___y_1346_ = v_a_1257_;
v___y_1347_ = v_a_1258_;
v___y_1348_ = v_a_1259_;
v___y_1349_ = v_a_1260_;
goto v___jp_1345_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v___f_1332_);
lean_dec(v_a_1322_);
lean_dec_ref(v___x_1301_);
lean_dec_ref(v_below_1253_);
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
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
v___jp_1333_:
{
lean_object* v_dummy_1338_; lean_object* v_nargs_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_6819__overap_1343_; lean_object* v___x_1344_; 
v_dummy_1338_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1339_ = l_Lean_Expr_getAppNumArgs(v_a_1322_);
lean_inc(v_nargs_1339_);
v___x_1340_ = lean_mk_array(v_nargs_1339_, v_dummy_1338_);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_nat_sub(v_nargs_1339_, v___x_1341_);
lean_dec(v_nargs_1339_);
v___x_6819__overap_1343_ = l_Lean_Expr_withAppAux___redArg(v___f_1332_, v_a_1322_, v___x_1340_, v___x_1342_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
v___x_1344_ = lean_apply_5(v___x_6819__overap_1343_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, lean_box(0));
return v___x_1344_;
}
v___jp_1345_:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Meta_isTypeCorrect(v_below_1253_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; uint8_t v___x_1352_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = lean_unbox(v_a_1351_);
lean_dec(v_a_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v_a_1354_; uint8_t v___x_1355_; 
v___x_1353_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1323_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref(v___x_1353_);
v___x_1355_ = lean_unbox(v_a_1354_);
lean_dec(v_a_1354_);
if (v___x_1355_ == 0)
{
lean_dec_ref(v___x_1301_);
v___y_1334_ = v___y_1346_;
v___y_1335_ = v___y_1347_;
v___y_1336_ = v___y_1348_;
v___y_1337_ = v___y_1349_;
goto v___jp_1333_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_6827__overap_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
lean_inc_ref(v_toMonadRef_1320_);
v___x_6827__overap_1357_ = l_Lean_addTrace___redArg(v___x_1301_, v___x_1302_, v_toMonadRef_1320_, v___x_1330_, v___x_1323_, v___x_1356_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v___y_1347_);
lean_inc_ref(v___y_1346_);
v___x_1358_ = lean_apply_5(v___x_6827__overap_1357_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, lean_box(0));
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_dec_ref_known(v___x_1358_, 1);
v___y_1334_ = v___y_1346_;
v___y_1335_ = v___y_1347_;
v___y_1336_ = v___y_1348_;
v___y_1337_ = v___y_1349_;
goto v___jp_1333_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec_ref(v___f_1332_);
lean_dec(v_a_1322_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1301_);
v___y_1334_ = v___y_1346_;
v___y_1335_ = v___y_1347_;
v___y_1336_ = v___y_1348_;
v___y_1337_ = v___y_1349_;
goto v___jp_1333_;
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v___f_1332_);
lean_dec(v_a_1322_);
lean_dec_ref(v___x_1301_);
v_a_1367_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1350_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1350_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v___x_1301_);
lean_dec_ref(v_k_1256_);
lean_dec_ref(v_positions_1255_);
lean_dec(v_numIndParams_1254_);
lean_dec_ref(v_below_1253_);
v_a_1389_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1321_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1321_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1403_, lean_object* v_numIndParams_1404_, lean_object* v_positions_1405_, lean_object* v_k_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1403_, v_numIndParams_1404_, v_positions_1405_, v_k_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1413_, lean_object* v_inst_1414_, lean_object* v_below_1415_, lean_object* v_numIndParams_1416_, lean_object* v_positions_1417_, lean_object* v_k_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1415_, v_numIndParams_1416_, v_positions_1417_, v_k_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1425_, lean_object* v_inst_1426_, lean_object* v_below_1427_, lean_object* v_numIndParams_1428_, lean_object* v_positions_1429_, lean_object* v_k_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1425_, v_inst_1426_, v_below_1427_, v_numIndParams_1428_, v_positions_1429_, v_k_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_inst_1426_);
return v_res_1436_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_unsigned_to_nat(32u);
v___x_1438_ = lean_mk_empty_array_with_capacity(v___x_1437_);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1440_ = ((size_t)5ULL);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_unsigned_to_nat(32u);
v___x_1443_ = lean_mk_empty_array_with_capacity(v___x_1442_);
v___x_1444_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1445_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___x_1443_);
lean_ctor_set(v___x_1445_, 2, v___x_1441_);
lean_ctor_set(v___x_1445_, 3, v___x_1441_);
lean_ctor_set_usize(v___x_1445_, 4, v___x_1440_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; lean_object* v_traceState_1449_; lean_object* v_traces_1450_; lean_object* v___x_1451_; lean_object* v_traceState_1452_; lean_object* v_env_1453_; lean_object* v_nextMacroScope_1454_; lean_object* v_ngen_1455_; lean_object* v_auxDeclNGen_1456_; lean_object* v_cache_1457_; lean_object* v_messages_1458_; lean_object* v_infoState_1459_; lean_object* v_snapshotTasks_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1479_; 
v___x_1448_ = lean_st_ref_get(v___y_1446_);
v_traceState_1449_ = lean_ctor_get(v___x_1448_, 4);
lean_inc_ref(v_traceState_1449_);
lean_dec(v___x_1448_);
v_traces_1450_ = lean_ctor_get(v_traceState_1449_, 0);
lean_inc_ref(v_traces_1450_);
lean_dec_ref(v_traceState_1449_);
v___x_1451_ = lean_st_ref_take(v___y_1446_);
v_traceState_1452_ = lean_ctor_get(v___x_1451_, 4);
v_env_1453_ = lean_ctor_get(v___x_1451_, 0);
v_nextMacroScope_1454_ = lean_ctor_get(v___x_1451_, 1);
v_ngen_1455_ = lean_ctor_get(v___x_1451_, 2);
v_auxDeclNGen_1456_ = lean_ctor_get(v___x_1451_, 3);
v_cache_1457_ = lean_ctor_get(v___x_1451_, 5);
v_messages_1458_ = lean_ctor_get(v___x_1451_, 6);
v_infoState_1459_ = lean_ctor_get(v___x_1451_, 7);
v_snapshotTasks_1460_ = lean_ctor_get(v___x_1451_, 8);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1462_ = v___x_1451_;
v_isShared_1463_ = v_isSharedCheck_1479_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_snapshotTasks_1460_);
lean_inc(v_infoState_1459_);
lean_inc(v_messages_1458_);
lean_inc(v_cache_1457_);
lean_inc(v_traceState_1452_);
lean_inc(v_auxDeclNGen_1456_);
lean_inc(v_ngen_1455_);
lean_inc(v_nextMacroScope_1454_);
lean_inc(v_env_1453_);
lean_dec(v___x_1451_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1479_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
uint64_t v_tid_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1477_; 
v_tid_1464_ = lean_ctor_get_uint64(v_traceState_1452_, sizeof(void*)*1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_traceState_1452_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_traceState_1452_, 0);
lean_dec(v_unused_1478_);
v___x_1466_ = v_traceState_1452_;
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_traceState_1452_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1468_);
lean_ctor_set_uint64(v_reuseFailAlloc_1476_, sizeof(void*)*1, v_tid_1464_);
v___x_1470_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 4, v___x_1470_);
v___x_1472_ = v___x_1462_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_env_1453_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_nextMacroScope_1454_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_ngen_1455_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_auxDeclNGen_1456_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1475_, 5, v_cache_1457_);
lean_ctor_set(v_reuseFailAlloc_1475_, 6, v_messages_1458_);
lean_ctor_set(v_reuseFailAlloc_1475_, 7, v_infoState_1459_);
lean_ctor_set(v_reuseFailAlloc_1475_, 8, v_snapshotTasks_1460_);
v___x_1472_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_st_ref_put(v___y_1446_, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_traces_1450_);
return v___x_1474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1480_);
lean_dec(v___y_1480_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1495_, lean_object* v_opt_1496_){
_start:
{
lean_object* v_name_1497_; lean_object* v_defValue_1498_; lean_object* v_map_1499_; lean_object* v___x_1500_; 
v_name_1497_ = lean_ctor_get(v_opt_1496_, 0);
v_defValue_1498_ = lean_ctor_get(v_opt_1496_, 1);
v_map_1499_ = lean_ctor_get(v_opts_1495_, 0);
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1499_, v_name_1497_);
if (lean_obj_tag(v___x_1500_) == 0)
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_unbox(v_defValue_1498_);
return v___x_1501_;
}
else
{
lean_object* v_val_1502_; 
v_val_1502_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v___x_1500_, 1);
if (lean_obj_tag(v_val_1502_) == 1)
{
uint8_t v_v_1503_; 
v_v_1503_ = lean_ctor_get_uint8(v_val_1502_, 0);
lean_dec_ref_known(v_val_1502_, 0);
return v_v_1503_;
}
else
{
uint8_t v___x_1504_; 
lean_dec(v_val_1502_);
v___x_1504_ = lean_unbox(v_defValue_1498_);
return v___x_1504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1505_, lean_object* v_opt_1506_){
_start:
{
uint8_t v_res_1507_; lean_object* v_r_1508_; 
v_res_1507_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1505_, v_opt_1506_);
lean_dec_ref(v_opt_1506_);
lean_dec_ref(v_opts_1505_);
v_r_1508_ = lean_box(v_res_1507_);
return v_r_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1509_, lean_object* v_fnIndex_1510_, lean_object* v_recArg_1511_, lean_object* v_below_1512_, lean_object* v_Cs_1513_, lean_object* v_belowDict_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_array_get_borrowed(v___x_1509_, v_Cs_1513_, v_fnIndex_1510_);
lean_inc(v___x_1520_);
v___x_1521_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1520_, v_belowDict_1514_, v_recArg_1511_, v_below_1512_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1522_, lean_object* v_fnIndex_1523_, lean_object* v_recArg_1524_, lean_object* v_below_1525_, lean_object* v_Cs_1526_, lean_object* v_belowDict_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1522_, v_fnIndex_1523_, v_recArg_1524_, v_below_1525_, v_Cs_1526_, v_belowDict_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec_ref(v_Cs_1526_);
lean_dec(v_fnIndex_1523_);
lean_dec_ref(v___x_1522_);
return v_res_1533_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1540_, lean_object* v_recArg_1541_, lean_object* v_x_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; 
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
v___x_1548_ = lean_infer_type(v_below_1540_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1563_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1563_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1563_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1554_ = l_Lean_MessageData_ofExpr(v_recArg_1541_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_MessageData_ofExpr(v_a_1549_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1559_);
v___x_1561_ = v___x_1551_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_recArg_1541_);
v_a_1564_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1548_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1548_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1572_, lean_object* v_recArg_1573_, lean_object* v_x_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1572_, v_recArg_1573_, v_x_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec_ref(v_x_1574_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t v_sz_1581_, size_t v_i_1582_, lean_object* v_bs_1583_){
_start:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_usize_dec_lt(v_i_1582_, v_sz_1581_);
if (v___x_1584_ == 0)
{
return v_bs_1583_;
}
else
{
lean_object* v_v_1585_; lean_object* v_msg_1586_; lean_object* v___x_1587_; lean_object* v_bs_x27_1588_; size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v_v_1585_ = lean_array_uget_borrowed(v_bs_1583_, v_i_1582_);
v_msg_1586_ = lean_ctor_get(v_v_1585_, 1);
lean_inc_ref(v_msg_1586_);
v___x_1587_ = lean_unsigned_to_nat(0u);
v_bs_x27_1588_ = lean_array_uset(v_bs_1583_, v_i_1582_, v___x_1587_);
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_add(v_i_1582_, v___x_1589_);
v___x_1591_ = lean_array_uset(v_bs_x27_1588_, v_i_1582_, v_msg_1586_);
v_i_1582_ = v___x_1590_;
v_bs_1583_ = v___x_1591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1593_, lean_object* v_i_1594_, lean_object* v_bs_1595_){
_start:
{
size_t v_sz_boxed_1596_; size_t v_i_boxed_1597_; lean_object* v_res_1598_; 
v_sz_boxed_1596_ = lean_unbox_usize(v_sz_1593_);
lean_dec(v_sz_1593_);
v_i_boxed_1597_ = lean_unbox_usize(v_i_1594_);
lean_dec(v_i_1594_);
v_res_1598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_boxed_1596_, v_i_boxed_1597_, v_bs_1595_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_oldTraces_1599_, lean_object* v_data_1600_, lean_object* v_ref_1601_, lean_object* v_msg_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_fileName_1608_; lean_object* v_fileMap_1609_; lean_object* v_options_1610_; lean_object* v_currRecDepth_1611_; lean_object* v_maxRecDepth_1612_; lean_object* v_ref_1613_; lean_object* v_currNamespace_1614_; lean_object* v_openDecls_1615_; lean_object* v_initHeartbeats_1616_; lean_object* v_maxHeartbeats_1617_; lean_object* v_quotContext_1618_; lean_object* v_currMacroScope_1619_; uint8_t v_diag_1620_; lean_object* v_cancelTk_x3f_1621_; uint8_t v_suppressElabErrors_1622_; lean_object* v_inheritedTraceOptions_1623_; lean_object* v___x_1624_; lean_object* v_traceState_1625_; lean_object* v_traces_1626_; lean_object* v_ref_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; size_t v_sz_1630_; size_t v___x_1631_; lean_object* v___x_1632_; lean_object* v_msg_1633_; lean_object* v___x_1634_; lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1672_; 
v_fileName_1608_ = lean_ctor_get(v___y_1605_, 0);
v_fileMap_1609_ = lean_ctor_get(v___y_1605_, 1);
v_options_1610_ = lean_ctor_get(v___y_1605_, 2);
v_currRecDepth_1611_ = lean_ctor_get(v___y_1605_, 3);
v_maxRecDepth_1612_ = lean_ctor_get(v___y_1605_, 4);
v_ref_1613_ = lean_ctor_get(v___y_1605_, 5);
v_currNamespace_1614_ = lean_ctor_get(v___y_1605_, 6);
v_openDecls_1615_ = lean_ctor_get(v___y_1605_, 7);
v_initHeartbeats_1616_ = lean_ctor_get(v___y_1605_, 8);
v_maxHeartbeats_1617_ = lean_ctor_get(v___y_1605_, 9);
v_quotContext_1618_ = lean_ctor_get(v___y_1605_, 10);
v_currMacroScope_1619_ = lean_ctor_get(v___y_1605_, 11);
v_diag_1620_ = lean_ctor_get_uint8(v___y_1605_, sizeof(void*)*14);
v_cancelTk_x3f_1621_ = lean_ctor_get(v___y_1605_, 12);
v_suppressElabErrors_1622_ = lean_ctor_get_uint8(v___y_1605_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1623_ = lean_ctor_get(v___y_1605_, 13);
v___x_1624_ = lean_st_ref_get(v___y_1606_);
v_traceState_1625_ = lean_ctor_get(v___x_1624_, 4);
lean_inc_ref(v_traceState_1625_);
lean_dec(v___x_1624_);
v_traces_1626_ = lean_ctor_get(v_traceState_1625_, 0);
lean_inc_ref(v_traces_1626_);
lean_dec_ref(v_traceState_1625_);
v_ref_1627_ = l_Lean_replaceRef(v_ref_1601_, v_ref_1613_);
lean_inc_ref(v_inheritedTraceOptions_1623_);
lean_inc(v_cancelTk_x3f_1621_);
lean_inc(v_currMacroScope_1619_);
lean_inc(v_quotContext_1618_);
lean_inc(v_maxHeartbeats_1617_);
lean_inc(v_initHeartbeats_1616_);
lean_inc(v_openDecls_1615_);
lean_inc(v_currNamespace_1614_);
lean_inc(v_maxRecDepth_1612_);
lean_inc(v_currRecDepth_1611_);
lean_inc_ref(v_options_1610_);
lean_inc_ref(v_fileMap_1609_);
lean_inc_ref(v_fileName_1608_);
v___x_1628_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1628_, 0, v_fileName_1608_);
lean_ctor_set(v___x_1628_, 1, v_fileMap_1609_);
lean_ctor_set(v___x_1628_, 2, v_options_1610_);
lean_ctor_set(v___x_1628_, 3, v_currRecDepth_1611_);
lean_ctor_set(v___x_1628_, 4, v_maxRecDepth_1612_);
lean_ctor_set(v___x_1628_, 5, v_ref_1627_);
lean_ctor_set(v___x_1628_, 6, v_currNamespace_1614_);
lean_ctor_set(v___x_1628_, 7, v_openDecls_1615_);
lean_ctor_set(v___x_1628_, 8, v_initHeartbeats_1616_);
lean_ctor_set(v___x_1628_, 9, v_maxHeartbeats_1617_);
lean_ctor_set(v___x_1628_, 10, v_quotContext_1618_);
lean_ctor_set(v___x_1628_, 11, v_currMacroScope_1619_);
lean_ctor_set(v___x_1628_, 12, v_cancelTk_x3f_1621_);
lean_ctor_set(v___x_1628_, 13, v_inheritedTraceOptions_1623_);
lean_ctor_set_uint8(v___x_1628_, sizeof(void*)*14, v_diag_1620_);
lean_ctor_set_uint8(v___x_1628_, sizeof(void*)*14 + 1, v_suppressElabErrors_1622_);
v___x_1629_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1626_);
lean_dec_ref(v_traces_1626_);
v_sz_1630_ = lean_array_size(v___x_1629_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1630_, v___x_1631_, v___x_1629_);
v_msg_1633_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1633_, 0, v_data_1600_);
lean_ctor_set(v_msg_1633_, 1, v_msg_1602_);
lean_ctor_set(v_msg_1633_, 2, v___x_1632_);
v___x_1634_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1633_, v___y_1603_, v___y_1604_, v___x_1628_, v___y_1606_);
lean_dec_ref_known(v___x_1628_, 14);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1672_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1672_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v_traceState_1640_; lean_object* v_env_1641_; lean_object* v_nextMacroScope_1642_; lean_object* v_ngen_1643_; lean_object* v_auxDeclNGen_1644_; lean_object* v_cache_1645_; lean_object* v_messages_1646_; lean_object* v_infoState_1647_; lean_object* v_snapshotTasks_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1671_; 
v___x_1639_ = lean_st_ref_take(v___y_1606_);
v_traceState_1640_ = lean_ctor_get(v___x_1639_, 4);
v_env_1641_ = lean_ctor_get(v___x_1639_, 0);
v_nextMacroScope_1642_ = lean_ctor_get(v___x_1639_, 1);
v_ngen_1643_ = lean_ctor_get(v___x_1639_, 2);
v_auxDeclNGen_1644_ = lean_ctor_get(v___x_1639_, 3);
v_cache_1645_ = lean_ctor_get(v___x_1639_, 5);
v_messages_1646_ = lean_ctor_get(v___x_1639_, 6);
v_infoState_1647_ = lean_ctor_get(v___x_1639_, 7);
v_snapshotTasks_1648_ = lean_ctor_get(v___x_1639_, 8);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1650_ = v___x_1639_;
v_isShared_1651_ = v_isSharedCheck_1671_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_snapshotTasks_1648_);
lean_inc(v_infoState_1647_);
lean_inc(v_messages_1646_);
lean_inc(v_cache_1645_);
lean_inc(v_traceState_1640_);
lean_inc(v_auxDeclNGen_1644_);
lean_inc(v_ngen_1643_);
lean_inc(v_nextMacroScope_1642_);
lean_inc(v_env_1641_);
lean_dec(v___x_1639_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1671_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
uint64_t v_tid_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1669_; 
v_tid_1652_ = lean_ctor_get_uint64(v_traceState_1640_, sizeof(void*)*1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_traceState_1640_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v_traceState_1640_, 0);
lean_dec(v_unused_1670_);
v___x_1654_ = v_traceState_1640_;
v_isShared_1655_ = v_isSharedCheck_1669_;
goto v_resetjp_1653_;
}
else
{
lean_dec(v_traceState_1640_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1669_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_ref_1601_);
lean_ctor_set(v___x_1656_, 1, v_a_1635_);
v___x_1657_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1599_, v___x_1656_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1657_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1657_);
lean_ctor_set_uint64(v_reuseFailAlloc_1668_, sizeof(void*)*1, v_tid_1652_);
v___x_1659_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 4, v___x_1659_);
v___x_1661_ = v___x_1650_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_env_1641_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_nextMacroScope_1642_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_ngen_1643_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_auxDeclNGen_1644_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1667_, 5, v_cache_1645_);
lean_ctor_set(v_reuseFailAlloc_1667_, 6, v_messages_1646_);
lean_ctor_set(v_reuseFailAlloc_1667_, 7, v_infoState_1647_);
lean_ctor_set(v_reuseFailAlloc_1667_, 8, v_snapshotTasks_1648_);
v___x_1661_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = lean_st_ref_put(v___y_1606_, v___x_1661_);
v___x_1663_ = lean_box(0);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1663_);
v___x_1665_ = v___x_1637_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1673_, lean_object* v_data_1674_, lean_object* v_ref_1675_, lean_object* v_msg_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1673_, v_data_1674_, v_ref_1675_, v_msg_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1683_, lean_object* v_opt_1684_){
_start:
{
lean_object* v_name_1685_; lean_object* v_defValue_1686_; lean_object* v_map_1687_; lean_object* v___x_1688_; 
v_name_1685_ = lean_ctor_get(v_opt_1684_, 0);
v_defValue_1686_ = lean_ctor_get(v_opt_1684_, 1);
v_map_1687_ = lean_ctor_get(v_opts_1683_, 0);
v___x_1688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1687_, v_name_1685_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_inc(v_defValue_1686_);
return v_defValue_1686_;
}
else
{
lean_object* v_val_1689_; 
v_val_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v___x_1688_, 1);
if (lean_obj_tag(v_val_1689_) == 3)
{
lean_object* v_v_1690_; 
v_v_1690_ = lean_ctor_get(v_val_1689_, 0);
lean_inc(v_v_1690_);
lean_dec_ref_known(v_val_1689_, 1);
return v_v_1690_;
}
else
{
lean_dec(v_val_1689_);
lean_inc(v_defValue_1686_);
return v_defValue_1686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1691_, lean_object* v_opt_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1691_, v_opt_1692_);
lean_dec_ref(v_opt_1692_);
lean_dec_ref(v_opts_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1694_){
_start:
{
if (lean_obj_tag(v_e_1694_) == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = 2;
return v___x_1695_;
}
else
{
lean_object* v_a_1696_; uint8_t v___x_1697_; 
v_a_1696_ = lean_ctor_get(v_e_1694_, 0);
v___x_1697_ = l_Lean_Expr_hasSyntheticSorry(v_a_1696_);
if (v___x_1697_ == 0)
{
uint8_t v___x_1698_; 
v___x_1698_ = 0;
return v___x_1698_;
}
else
{
uint8_t v___x_1699_; 
v___x_1699_ = 1;
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1700_);
lean_dec_ref(v_e_1700_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_a_1705_ = lean_ctor_get(v_x_1703_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_x_1703_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v_x_1703_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v_x_1703_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 1);
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1713_ = lean_ctor_get(v_x_1703_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1703_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v_x_1703_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v_x_1703_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 0);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1721_);
return v_res_1723_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1727_; double v___x_1728_; 
v___x_1727_ = lean_unsigned_to_nat(1000u);
v___x_1728_ = lean_float_of_nat(v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1729_, uint8_t v_collapsed_1730_, lean_object* v_tag_1731_, lean_object* v_opts_1732_, uint8_t v_clsEnabled_1733_, lean_object* v_oldTraces_1734_, lean_object* v_msg_1735_, lean_object* v_resStartStop_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_fst_1742_; lean_object* v_snd_1743_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v_data_1747_; lean_object* v_fst_1758_; lean_object* v_snd_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; lean_object* v___y_1763_; lean_object* v_a_1764_; uint8_t v___y_1779_; double v___y_1810_; 
v_fst_1742_ = lean_ctor_get(v_resStartStop_1736_, 0);
lean_inc(v_fst_1742_);
v_snd_1743_ = lean_ctor_get(v_resStartStop_1736_, 1);
lean_inc(v_snd_1743_);
lean_dec_ref(v_resStartStop_1736_);
v_fst_1758_ = lean_ctor_get(v_snd_1743_, 0);
lean_inc(v_fst_1758_);
v_snd_1759_ = lean_ctor_get(v_snd_1743_, 1);
lean_inc(v_snd_1759_);
lean_dec(v_snd_1743_);
v___x_1760_ = l_Lean_trace_profiler;
v___x_1761_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1732_, v___x_1760_);
if (v___x_1761_ == 0)
{
v___y_1779_ = v___x_1761_;
goto v___jp_1778_;
}
else
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1816_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1732_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; double v___x_1819_; double v___x_1820_; double v___x_1821_; 
v___x_1817_ = l_Lean_trace_profiler_threshold;
v___x_1818_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1732_, v___x_1817_);
v___x_1819_ = lean_float_of_nat(v___x_1818_);
v___x_1820_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2);
v___x_1821_ = lean_float_div(v___x_1819_, v___x_1820_);
v___y_1810_ = v___x_1821_;
goto v___jp_1809_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; double v___x_1824_; 
v___x_1822_ = l_Lean_trace_profiler_threshold;
v___x_1823_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1732_, v___x_1822_);
v___x_1824_ = lean_float_of_nat(v___x_1823_);
v___y_1810_ = v___x_1824_;
goto v___jp_1809_;
}
}
v___jp_1744_:
{
lean_object* v___x_1748_; 
lean_inc(v___y_1745_);
v___x_1748_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1734_, v_data_1747_, v___y_1745_, v___y_1746_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v___x_1749_; 
lean_dec_ref_known(v___x_1748_, 1);
v___x_1749_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1742_);
return v___x_1749_;
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_fst_1742_);
v_a_1750_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1748_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1748_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
v___jp_1762_:
{
uint8_t v_result_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; double v___x_1768_; lean_object* v_data_1769_; 
v_result_1765_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1742_);
v___x_1766_ = lean_box(v_result_1765_);
v___x_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
v___x_1768_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1731_);
lean_inc_ref(v___x_1767_);
lean_inc(v_cls_1729_);
v_data_1769_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1769_, 0, v_cls_1729_);
lean_ctor_set(v_data_1769_, 1, v___x_1767_);
lean_ctor_set(v_data_1769_, 2, v_tag_1731_);
lean_ctor_set_float(v_data_1769_, sizeof(void*)*3, v___x_1768_);
lean_ctor_set_float(v_data_1769_, sizeof(void*)*3 + 8, v___x_1768_);
lean_ctor_set_uint8(v_data_1769_, sizeof(void*)*3 + 16, v_collapsed_1730_);
if (v___x_1761_ == 0)
{
lean_dec_ref_known(v___x_1767_, 1);
lean_dec(v_snd_1759_);
lean_dec(v_fst_1758_);
lean_dec_ref(v_tag_1731_);
lean_dec(v_cls_1729_);
v___y_1745_ = v___y_1763_;
v___y_1746_ = v_a_1764_;
v_data_1747_ = v_data_1769_;
goto v___jp_1744_;
}
else
{
lean_object* v_data_1770_; double v___x_1771_; double v___x_1772_; 
lean_dec_ref_known(v_data_1769_, 3);
v_data_1770_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1770_, 0, v_cls_1729_);
lean_ctor_set(v_data_1770_, 1, v___x_1767_);
lean_ctor_set(v_data_1770_, 2, v_tag_1731_);
v___x_1771_ = lean_unbox_float(v_fst_1758_);
lean_dec(v_fst_1758_);
lean_ctor_set_float(v_data_1770_, sizeof(void*)*3, v___x_1771_);
v___x_1772_ = lean_unbox_float(v_snd_1759_);
lean_dec(v_snd_1759_);
lean_ctor_set_float(v_data_1770_, sizeof(void*)*3 + 8, v___x_1772_);
lean_ctor_set_uint8(v_data_1770_, sizeof(void*)*3 + 16, v_collapsed_1730_);
v___y_1745_ = v___y_1763_;
v___y_1746_ = v_a_1764_;
v_data_1747_ = v_data_1770_;
goto v___jp_1744_;
}
}
v___jp_1773_:
{
lean_object* v_ref_1774_; lean_object* v___x_1775_; 
v_ref_1774_ = lean_ctor_get(v___y_1739_, 5);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v_fst_1742_);
v___x_1775_ = lean_apply_6(v_msg_1735_, v_fst_1742_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, lean_box(0));
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v___y_1763_ = v_ref_1774_;
v_a_1764_ = v_a_1776_;
goto v___jp_1762_;
}
else
{
lean_object* v___x_1777_; 
lean_dec_ref_known(v___x_1775_, 1);
v___x_1777_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
v___y_1763_ = v_ref_1774_;
v_a_1764_ = v___x_1777_;
goto v___jp_1762_;
}
}
v___jp_1778_:
{
if (v_clsEnabled_1733_ == 0)
{
if (v___y_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v_traceState_1781_; lean_object* v_env_1782_; lean_object* v_nextMacroScope_1783_; lean_object* v_ngen_1784_; lean_object* v_auxDeclNGen_1785_; lean_object* v_cache_1786_; lean_object* v_messages_1787_; lean_object* v_infoState_1788_; lean_object* v_snapshotTasks_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_snd_1759_);
lean_dec(v_fst_1758_);
lean_dec_ref(v_msg_1735_);
lean_dec_ref(v_tag_1731_);
lean_dec(v_cls_1729_);
v___x_1780_ = lean_st_ref_take(v___y_1740_);
v_traceState_1781_ = lean_ctor_get(v___x_1780_, 4);
v_env_1782_ = lean_ctor_get(v___x_1780_, 0);
v_nextMacroScope_1783_ = lean_ctor_get(v___x_1780_, 1);
v_ngen_1784_ = lean_ctor_get(v___x_1780_, 2);
v_auxDeclNGen_1785_ = lean_ctor_get(v___x_1780_, 3);
v_cache_1786_ = lean_ctor_get(v___x_1780_, 5);
v_messages_1787_ = lean_ctor_get(v___x_1780_, 6);
v_infoState_1788_ = lean_ctor_get(v___x_1780_, 7);
v_snapshotTasks_1789_ = lean_ctor_get(v___x_1780_, 8);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1791_ = v___x_1780_;
v_isShared_1792_ = v_isSharedCheck_1808_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_snapshotTasks_1789_);
lean_inc(v_infoState_1788_);
lean_inc(v_messages_1787_);
lean_inc(v_cache_1786_);
lean_inc(v_traceState_1781_);
lean_inc(v_auxDeclNGen_1785_);
lean_inc(v_ngen_1784_);
lean_inc(v_nextMacroScope_1783_);
lean_inc(v_env_1782_);
lean_dec(v___x_1780_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1808_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
uint64_t v_tid_1793_; lean_object* v_traces_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1807_; 
v_tid_1793_ = lean_ctor_get_uint64(v_traceState_1781_, sizeof(void*)*1);
v_traces_1794_ = lean_ctor_get(v_traceState_1781_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_traceState_1781_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1796_ = v_traceState_1781_;
v_isShared_1797_ = v_isSharedCheck_1807_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_traces_1794_);
lean_dec(v_traceState_1781_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1807_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1798_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1734_, v_traces_1794_);
lean_dec_ref(v_traces_1794_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1798_);
v___x_1800_ = v___x_1796_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1798_);
lean_ctor_set_uint64(v_reuseFailAlloc_1806_, sizeof(void*)*1, v_tid_1793_);
v___x_1800_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1802_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 4, v___x_1800_);
v___x_1802_ = v___x_1791_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_env_1782_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_nextMacroScope_1783_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_ngen_1784_);
lean_ctor_set(v_reuseFailAlloc_1805_, 3, v_auxDeclNGen_1785_);
lean_ctor_set(v_reuseFailAlloc_1805_, 4, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1805_, 5, v_cache_1786_);
lean_ctor_set(v_reuseFailAlloc_1805_, 6, v_messages_1787_);
lean_ctor_set(v_reuseFailAlloc_1805_, 7, v_infoState_1788_);
lean_ctor_set(v_reuseFailAlloc_1805_, 8, v_snapshotTasks_1789_);
v___x_1802_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_st_ref_put(v___y_1740_, v___x_1802_);
v___x_1804_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1742_);
return v___x_1804_;
}
}
}
}
}
else
{
goto v___jp_1773_;
}
}
else
{
goto v___jp_1773_;
}
}
v___jp_1809_:
{
double v___x_1811_; double v___x_1812_; double v___x_1813_; uint8_t v___x_1814_; 
v___x_1811_ = lean_unbox_float(v_snd_1759_);
v___x_1812_ = lean_unbox_float(v_fst_1758_);
v___x_1813_ = lean_float_sub(v___x_1811_, v___x_1812_);
v___x_1814_ = lean_float_decLt(v___y_1810_, v___x_1813_);
v___y_1779_ = v___x_1814_;
goto v___jp_1778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1825_, lean_object* v_collapsed_1826_, lean_object* v_tag_1827_, lean_object* v_opts_1828_, lean_object* v_clsEnabled_1829_, lean_object* v_oldTraces_1830_, lean_object* v_msg_1831_, lean_object* v_resStartStop_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
uint8_t v_collapsed_boxed_1838_; uint8_t v_clsEnabled_boxed_1839_; lean_object* v_res_1840_; 
v_collapsed_boxed_1838_ = lean_unbox(v_collapsed_1826_);
v_clsEnabled_boxed_1839_ = lean_unbox(v_clsEnabled_1829_);
v_res_1840_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1825_, v_collapsed_boxed_1838_, v_tag_1827_, v_opts_1828_, v_clsEnabled_boxed_1839_, v_oldTraces_1830_, v_msg_1831_, v_resStartStop_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v_opts_1828_);
return v_res_1840_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1842_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1843_ = l_Lean_Name_append(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__1(void){
_start:
{
lean_object* v___x_1844_; double v___x_1845_; 
v___x_1844_ = lean_unsigned_to_nat(1000000000u);
v___x_1845_ = lean_float_of_nat(v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1846_, lean_object* v_numIndParams_1847_, lean_object* v_positions_1848_, lean_object* v_fnIndex_1849_, lean_object* v_recArg_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_options_1856_; lean_object* v_inheritedTraceOptions_1857_; uint8_t v_hasTrace_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; 
v_options_1856_ = lean_ctor_get(v_a_1853_, 2);
v_inheritedTraceOptions_1857_ = lean_ctor_get(v_a_1853_, 13);
v_hasTrace_1858_ = lean_ctor_get_uint8(v_options_1856_, sizeof(void*)*1);
v___x_1859_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1846_);
lean_inc_ref(v_recArg_1850_);
v___f_1860_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1860_, 0, v___x_1859_);
lean_closure_set(v___f_1860_, 1, v_fnIndex_1849_);
lean_closure_set(v___f_1860_, 2, v_recArg_1850_);
lean_closure_set(v___f_1860_, 3, v_below_1846_);
if (v_hasTrace_1858_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_recArg_1850_);
v___x_1861_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1846_, v_numIndParams_1847_, v_positions_1848_, v___f_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1861_;
}
else
{
lean_object* v___f_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v_a_1870_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v_a_1885_; 
lean_inc_ref(v_below_1846_);
v___f_1862_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1862_, 0, v_below_1846_);
lean_closure_set(v___f_1862_, 1, v_recArg_1850_);
v___x_1863_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1864_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1865_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1866_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1857_, v_options_1856_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = l_Lean_trace_profiler;
v___x_1936_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1856_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
lean_dec_ref(v___f_1862_);
v___x_1937_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1846_, v_numIndParams_1847_, v_positions_1848_, v___f_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1937_;
}
else
{
goto v___jp_1894_;
}
}
else
{
goto v___jp_1894_;
}
v___jp_1867_:
{
lean_object* v___x_1871_; double v___x_1872_; double v___x_1873_; double v___x_1874_; double v___x_1875_; double v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1871_ = lean_io_mono_nanos_now();
v___x_1872_ = lean_float_of_nat(v___y_1869_);
v___x_1873_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__1, &l_Lean_Elab_Structural_toBelow___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___closed__1);
v___x_1874_ = lean_float_div(v___x_1872_, v___x_1873_);
v___x_1875_ = lean_float_of_nat(v___x_1871_);
v___x_1876_ = lean_float_div(v___x_1875_, v___x_1873_);
v___x_1877_ = lean_box_float(v___x_1874_);
v___x_1878_ = lean_box_float(v___x_1876_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v_a_1870_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1863_, v_hasTrace_1858_, v___x_1864_, v_options_1856_, v___x_1866_, v___y_1868_, v___f_1862_, v___x_1880_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1881_;
}
v___jp_1882_:
{
lean_object* v___x_1886_; double v___x_1887_; double v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1886_ = lean_io_get_num_heartbeats();
v___x_1887_ = lean_float_of_nat(v___y_1883_);
v___x_1888_ = lean_float_of_nat(v___x_1886_);
v___x_1889_ = lean_box_float(v___x_1887_);
v___x_1890_ = lean_box_float(v___x_1888_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v_a_1885_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1863_, v_hasTrace_1858_, v___x_1864_, v_options_1856_, v___x_1866_, v___y_1884_, v___f_1862_, v___x_1892_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1893_;
}
v___jp_1894_:
{
lean_object* v___x_1895_; lean_object* v_a_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1895_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1854_);
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
v___x_1897_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1898_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1856_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_io_mono_nanos_now();
v___x_1900_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1846_, v_numIndParams_1847_, v_positions_1848_, v___f_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 1);
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v___y_1868_ = v_a_1896_;
v___y_1869_ = v___x_1899_;
v_a_1870_ = v___x_1906_;
goto v___jp_1867_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1900_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1900_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 0);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
v___y_1868_ = v_a_1896_;
v___y_1869_ = v___x_1899_;
v_a_1870_ = v___x_1914_;
goto v___jp_1867_;
}
}
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_io_get_num_heartbeats();
v___x_1918_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1846_, v_numIndParams_1847_, v_positions_1848_, v___f_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 1);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
v___y_1883_ = v___x_1917_;
v___y_1884_ = v_a_1896_;
v_a_1885_ = v___x_1924_;
goto v___jp_1882_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_a_1927_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1918_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1918_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 0);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
v___y_1883_ = v___x_1917_;
v___y_1884_ = v_a_1896_;
v_a_1885_ = v___x_1932_;
goto v___jp_1882_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1938_, lean_object* v_numIndParams_1939_, lean_object* v_positions_1940_, lean_object* v_fnIndex_1941_, lean_object* v_recArg_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Elab_Structural_toBelow(v_below_1938_, v_numIndParams_1939_, v_positions_1940_, v_fnIndex_1941_, v_recArg_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1950_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1957_, lean_object* v_x_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1957_, v_x_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1965_, lean_object* v___y_1966_, lean_object* v_b_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
lean_inc(v___y_1971_);
lean_inc_ref(v___y_1970_);
lean_inc(v___y_1969_);
lean_inc_ref(v___y_1968_);
lean_inc(v___y_1966_);
v___x_1973_ = lean_apply_7(v_k_1965_, v_b_1967_, v___y_1966_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, lean_box(0));
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_1974_, lean_object* v___y_1975_, lean_object* v_b_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_1974_, v___y_1975_, v_b_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1975_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_1983_, uint8_t v_bi_1984_, lean_object* v_type_1985_, lean_object* v_k_1986_, uint8_t v_kind_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___f_1994_; lean_object* v___x_1995_; 
lean_inc(v___y_1988_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1994_, 0, v_k_1986_);
lean_closure_set(v___f_1994_, 1, v___y_1988_);
v___x_1995_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1983_, v_bi_1984_, v_type_1985_, v___f_1994_, v_kind_1987_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1995_) == 0)
{
return v___x_1995_;
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_2004_, lean_object* v_bi_2005_, lean_object* v_type_2006_, lean_object* v_k_2007_, lean_object* v_kind_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v_bi_boxed_2015_; uint8_t v_kind_boxed_2016_; lean_object* v_res_2017_; 
v_bi_boxed_2015_ = lean_unbox(v_bi_2005_);
v_kind_boxed_2016_ = lean_unbox(v_kind_2008_);
v_res_2017_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2004_, v_bi_boxed_2015_, v_type_2006_, v_k_2007_, v_kind_boxed_2016_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2018_, lean_object* v_name_2019_, uint8_t v_bi_2020_, lean_object* v_type_2021_, lean_object* v_k_2022_, uint8_t v_kind_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2019_, v_bi_2020_, v_type_2021_, v_k_2022_, v_kind_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2031_, lean_object* v_name_2032_, lean_object* v_bi_2033_, lean_object* v_type_2034_, lean_object* v_k_2035_, lean_object* v_kind_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v_bi_boxed_2043_; uint8_t v_kind_boxed_2044_; lean_object* v_res_2045_; 
v_bi_boxed_2043_ = lean_unbox(v_bi_2033_);
v_kind_boxed_2044_ = lean_unbox(v_kind_2036_);
v_res_2045_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2031_, v_name_2032_, v_bi_boxed_2043_, v_type_2034_, v_k_2035_, v_kind_boxed_2044_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2046_, lean_object* v___y_2047_, lean_object* v_b_2048_, lean_object* v_c_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
lean_inc(v___y_2053_);
lean_inc_ref(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
lean_inc(v___y_2047_);
v___x_2055_ = lean_apply_8(v_k_2046_, v_b_2048_, v_c_2049_, v___y_2047_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, lean_box(0));
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2056_, lean_object* v___y_2057_, lean_object* v_b_2058_, lean_object* v_c_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2056_, v___y_2057_, v_b_2058_, v_c_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2057_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2066_, lean_object* v_maxFVars_2067_, lean_object* v_k_2068_, uint8_t v_cleanupAnnotations_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___f_2076_; uint8_t v___x_2077_; uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_inc(v___y_2070_);
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2076_, 0, v_k_2068_);
lean_closure_set(v___f_2076_, 1, v___y_2070_);
v___x_2077_ = 1;
v___x_2078_ = 0;
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_maxFVars_2067_);
v___x_2080_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2066_, v___x_2077_, v___x_2078_, v___x_2077_, v___x_2078_, v___x_2079_, v___f_2076_, v_cleanupAnnotations_2069_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec_ref_known(v___x_2079_, 1);
if (lean_obj_tag(v___x_2080_) == 0)
{
return v___x_2080_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2089_, lean_object* v_maxFVars_2090_, lean_object* v_k_2091_, lean_object* v_cleanupAnnotations_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2099_; lean_object* v_res_2100_; 
v_cleanupAnnotations_boxed_2099_ = lean_unbox(v_cleanupAnnotations_2092_);
v_res_2100_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2089_, v_maxFVars_2090_, v_k_2091_, v_cleanupAnnotations_boxed_2099_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2101_, lean_object* v_e_2102_, lean_object* v_maxFVars_2103_, lean_object* v_k_2104_, uint8_t v_cleanupAnnotations_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2102_, v_maxFVars_2103_, v_k_2104_, v_cleanupAnnotations_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_e_2114_, lean_object* v_maxFVars_2115_, lean_object* v_k_2116_, lean_object* v_cleanupAnnotations_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2124_; lean_object* v_res_2125_; 
v_cleanupAnnotations_boxed_2124_ = lean_unbox(v_cleanupAnnotations_2117_);
v_res_2125_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2113_, v_e_2114_, v_maxFVars_2115_, v_k_2116_, v_cleanupAnnotations_boxed_2124_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2126_, lean_object* v_msg_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_ref_2133_; lean_object* v___x_2134_; lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2179_; 
v_ref_2133_ = lean_ctor_get(v___y_2130_, 5);
v___x_2134_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2179_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2179_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v_traceState_2140_; lean_object* v_env_2141_; lean_object* v_nextMacroScope_2142_; lean_object* v_ngen_2143_; lean_object* v_auxDeclNGen_2144_; lean_object* v_cache_2145_; lean_object* v_messages_2146_; lean_object* v_infoState_2147_; lean_object* v_snapshotTasks_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2178_; 
v___x_2139_ = lean_st_ref_take(v___y_2131_);
v_traceState_2140_ = lean_ctor_get(v___x_2139_, 4);
v_env_2141_ = lean_ctor_get(v___x_2139_, 0);
v_nextMacroScope_2142_ = lean_ctor_get(v___x_2139_, 1);
v_ngen_2143_ = lean_ctor_get(v___x_2139_, 2);
v_auxDeclNGen_2144_ = lean_ctor_get(v___x_2139_, 3);
v_cache_2145_ = lean_ctor_get(v___x_2139_, 5);
v_messages_2146_ = lean_ctor_get(v___x_2139_, 6);
v_infoState_2147_ = lean_ctor_get(v___x_2139_, 7);
v_snapshotTasks_2148_ = lean_ctor_get(v___x_2139_, 8);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2150_ = v___x_2139_;
v_isShared_2151_ = v_isSharedCheck_2178_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_snapshotTasks_2148_);
lean_inc(v_infoState_2147_);
lean_inc(v_messages_2146_);
lean_inc(v_cache_2145_);
lean_inc(v_traceState_2140_);
lean_inc(v_auxDeclNGen_2144_);
lean_inc(v_ngen_2143_);
lean_inc(v_nextMacroScope_2142_);
lean_inc(v_env_2141_);
lean_dec(v___x_2139_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2178_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
uint64_t v_tid_2152_; lean_object* v_traces_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2177_; 
v_tid_2152_ = lean_ctor_get_uint64(v_traceState_2140_, sizeof(void*)*1);
v_traces_2153_ = lean_ctor_get(v_traceState_2140_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_traceState_2140_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2155_ = v_traceState_2140_;
v_isShared_2156_ = v_isSharedCheck_2177_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_traces_2153_);
lean_dec(v_traceState_2140_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2177_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; double v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2159_ = 0;
v___x_2160_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2161_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2161_, 0, v_cls_2126_);
lean_ctor_set(v___x_2161_, 1, v___x_2157_);
lean_ctor_set(v___x_2161_, 2, v___x_2160_);
lean_ctor_set_float(v___x_2161_, sizeof(void*)*3, v___x_2158_);
lean_ctor_set_float(v___x_2161_, sizeof(void*)*3 + 8, v___x_2158_);
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*3 + 16, v___x_2159_);
v___x_2162_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2163_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v_a_2135_);
lean_ctor_set(v___x_2163_, 2, v___x_2162_);
lean_inc(v_ref_2133_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_ref_2133_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_PersistentArray_push___redArg(v_traces_2153_, v___x_2164_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2165_);
v___x_2167_ = v___x_2155_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2165_);
lean_ctor_set_uint64(v_reuseFailAlloc_2176_, sizeof(void*)*1, v_tid_2152_);
v___x_2167_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 4, v___x_2167_);
v___x_2169_ = v___x_2150_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_env_2141_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_nextMacroScope_2142_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_ngen_2143_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_auxDeclNGen_2144_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2175_, 5, v_cache_2145_);
lean_ctor_set(v_reuseFailAlloc_2175_, 6, v_messages_2146_);
lean_ctor_set(v_reuseFailAlloc_2175_, 7, v_infoState_2147_);
lean_ctor_set(v_reuseFailAlloc_2175_, 8, v_snapshotTasks_2148_);
v___x_2169_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = lean_st_ref_put(v___y_2131_, v___x_2169_);
v___x_2171_ = lean_box(0);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2171_);
v___x_2173_ = v___x_2137_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2180_, lean_object* v_msg_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2180_, v_msg_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2187_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2188_, lean_object* v_as_2189_, size_t v_i_2190_, size_t v_stop_2191_){
_start:
{
uint8_t v___x_2196_; 
v___x_2196_ = lean_usize_dec_eq(v_i_2190_, v_stop_2191_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v_fnName_2198_; lean_object* v_recArgPos_2199_; uint8_t v___x_2200_; 
v___x_2197_ = lean_array_uget_borrowed(v_as_2189_, v_i_2190_);
v_fnName_2198_ = lean_ctor_get(v___x_2197_, 0);
v_recArgPos_2199_ = lean_ctor_get(v___x_2197_, 2);
lean_inc(v_recArgPos_2199_);
lean_inc(v_fnName_2198_);
v___x_2200_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2198_, v_recArgPos_2199_, v_e_2188_);
if (v___x_2200_ == 0)
{
goto v___jp_2192_;
}
else
{
if (v___x_2200_ == 0)
{
goto v___jp_2192_;
}
else
{
return v___x_2200_;
}
}
}
else
{
uint8_t v___x_2201_; 
v___x_2201_ = 0;
return v___x_2201_;
}
v___jp_2192_:
{
size_t v___x_2193_; size_t v___x_2194_; 
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2190_, v___x_2193_);
v_i_2190_ = v___x_2194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2202_, lean_object* v_as_2203_, lean_object* v_i_2204_, lean_object* v_stop_2205_){
_start:
{
size_t v_i_boxed_2206_; size_t v_stop_boxed_2207_; uint8_t v_res_2208_; lean_object* v_r_2209_; 
v_i_boxed_2206_ = lean_unbox_usize(v_i_2204_);
lean_dec(v_i_2204_);
v_stop_boxed_2207_ = lean_unbox_usize(v_stop_2205_);
lean_dec(v_stop_2205_);
v_res_2208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2202_, v_as_2203_, v_i_boxed_2206_, v_stop_boxed_2207_);
lean_dec_ref(v_as_2203_);
lean_dec_ref(v_e_2202_);
v_r_2209_ = lean_box(v_res_2208_);
return v_r_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2210_, lean_object* v_____do__lift_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_options_2218_; uint8_t v_hasTrace_2219_; 
v_options_2218_ = lean_ctor_get(v___y_2215_, 2);
v_hasTrace_2219_ = lean_ctor_get_uint8(v_options_2218_, sizeof(void*)*1);
if (v_hasTrace_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec(v___x_2210_);
v___x_2220_ = lean_box(v_hasTrace_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2223_ = l_Lean_Name_append(v___x_2222_, v___x_2210_);
v___x_2224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2211_, v_options_2218_, v___x_2223_);
lean_dec(v___x_2223_);
v___x_2225_ = lean_box(v___x_2224_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2227_, lean_object* v_____do__lift_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2227_, v_____do__lift_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v_____do__lift_2228_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; lean_object* v_env_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2239_ = lean_st_ref_get(v___y_2237_);
v_env_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc_ref(v_env_2240_);
lean_dec(v___x_2239_);
v___x_2241_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2240_, v_declName_2236_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2243_, v___y_2244_);
lean_dec(v___y_2244_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; lean_object* v_toApplicative_2255_; lean_object* v_toFunctor_2256_; lean_object* v_toSeq_2257_; lean_object* v_toSeqLeft_2258_; lean_object* v_toSeqRight_2259_; lean_object* v___f_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; lean_object* v___f_2266_; lean_object* v___f_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_toApplicative_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2303_; 
v___x_2254_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2255_ = lean_ctor_get(v___x_2254_, 0);
v_toFunctor_2256_ = lean_ctor_get(v_toApplicative_2255_, 0);
v_toSeq_2257_ = lean_ctor_get(v_toApplicative_2255_, 2);
v_toSeqLeft_2258_ = lean_ctor_get(v_toApplicative_2255_, 3);
v_toSeqRight_2259_ = lean_ctor_get(v_toApplicative_2255_, 4);
v___f_2260_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2256_, 2);
v___f_2262_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2262_, 0, v_toFunctor_2256_);
v___f_2263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2263_, 0, v_toFunctor_2256_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___f_2262_);
lean_ctor_set(v___x_2264_, 1, v___f_2263_);
lean_inc(v_toSeqRight_2259_);
v___f_2265_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2265_, 0, v_toSeqRight_2259_);
lean_inc(v_toSeqLeft_2258_);
v___f_2266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2266_, 0, v_toSeqLeft_2258_);
lean_inc(v_toSeq_2257_);
v___f_2267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2267_, 0, v_toSeq_2257_);
v___x_2268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2264_);
lean_ctor_set(v___x_2268_, 1, v___f_2260_);
lean_ctor_set(v___x_2268_, 2, v___f_2267_);
lean_ctor_set(v___x_2268_, 3, v___f_2266_);
lean_ctor_set(v___x_2268_, 4, v___f_2265_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___f_2261_);
v___x_2270_ = l_StateRefT_x27_instMonad___redArg(v___x_2269_);
v_toApplicative_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v___x_2270_, 1);
lean_dec(v_unused_2304_);
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2303_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_toApplicative_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2303_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_toFunctor_2275_; lean_object* v_toSeq_2276_; lean_object* v_toSeqLeft_2277_; lean_object* v_toSeqRight_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2301_; 
v_toFunctor_2275_ = lean_ctor_get(v_toApplicative_2271_, 0);
v_toSeq_2276_ = lean_ctor_get(v_toApplicative_2271_, 2);
v_toSeqLeft_2277_ = lean_ctor_get(v_toApplicative_2271_, 3);
v_toSeqRight_2278_ = lean_ctor_get(v_toApplicative_2271_, 4);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_toApplicative_2271_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v_toApplicative_2271_, 1);
lean_dec(v_unused_2302_);
v___x_2280_ = v_toApplicative_2271_;
v_isShared_2281_ = v_isSharedCheck_2301_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_toSeqRight_2278_);
lean_inc(v_toSeqLeft_2277_);
lean_inc(v_toSeq_2276_);
lean_inc(v_toFunctor_2275_);
lean_dec(v_toApplicative_2271_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2301_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; lean_object* v___f_2287_; lean_object* v___f_2288_; lean_object* v___f_2289_; lean_object* v___x_2291_; 
v___f_2282_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2283_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2275_);
v___f_2284_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2284_, 0, v_toFunctor_2275_);
v___f_2285_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2285_, 0, v_toFunctor_2275_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___f_2284_);
lean_ctor_set(v___x_2286_, 1, v___f_2285_);
v___f_2287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2287_, 0, v_toSeqRight_2278_);
v___f_2288_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2288_, 0, v_toSeqLeft_2277_);
v___f_2289_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2289_, 0, v_toSeq_2276_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 4, v___f_2287_);
lean_ctor_set(v___x_2280_, 3, v___f_2288_);
lean_ctor_set(v___x_2280_, 2, v___f_2289_);
lean_ctor_set(v___x_2280_, 1, v___f_2282_);
lean_ctor_set(v___x_2280_, 0, v___x_2286_);
v___x_2291_ = v___x_2280_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___f_2282_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v___f_2289_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v___f_2288_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v___f_2287_);
v___x_2291_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2293_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 1, v___f_2283_);
lean_ctor_set(v___x_2273_, 0, v___x_2291_);
v___x_2293_ = v___x_2273_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v___f_2283_);
v___x_2293_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_23815__overap_2297_; lean_object* v___x_2298_; 
v___x_2294_ = l_StateRefT_x27_instMonad___redArg(v___x_2293_);
v___x_2295_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2296_ = l_instInhabitedOfMonad___redArg(v___x_2294_, v___x_2295_);
v___x_23815__overap_2297_ = lean_panic_fn_borrowed(v___x_2296_, v_msg_2247_);
lean_dec(v___x_2296_);
lean_inc(v___y_2252_);
lean_inc_ref(v___y_2251_);
lean_inc(v___y_2250_);
lean_inc_ref(v___y_2249_);
lean_inc(v___y_2248_);
v___x_2298_ = lean_apply_6(v___x_23815__overap_2297_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, lean_box(0));
return v___x_2298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
return v_res_2312_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
lean_ctor_set(v___x_2318_, 2, v___x_2317_);
lean_ctor_set(v___x_2318_, 3, v___x_2317_);
lean_ctor_set(v___x_2318_, 4, v___x_2316_);
lean_ctor_set(v___x_2318_, 5, v___x_2316_);
lean_ctor_set(v___x_2318_, 6, v___x_2316_);
lean_ctor_set(v___x_2318_, 7, v___x_2316_);
lean_ctor_set(v___x_2318_, 8, v___x_2316_);
lean_ctor_set(v___x_2318_, 9, v___x_2316_);
lean_ctor_set(v___x_2318_, 10, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = lean_unsigned_to_nat(32u);
v___x_2320_ = lean_mk_empty_array_with_capacity(v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2322_ = ((size_t)5ULL);
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = lean_unsigned_to_nat(32u);
v___x_2325_ = lean_mk_empty_array_with_capacity(v___x_2324_);
v___x_2326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2327_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
lean_ctor_set(v___x_2327_, 2, v___x_2323_);
lean_ctor_set(v___x_2327_, 3, v___x_2323_);
lean_ctor_set_usize(v___x_2327_, 4, v___x_2322_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2328_ = lean_box(1);
v___x_2329_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2330_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v___x_2329_);
lean_ctor_set(v___x_2331_, 2, v___x_2328_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
return v___x_2334_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2337_ = l_Lean_stringToMessageData(v___x_2336_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2340_ = l_Lean_stringToMessageData(v___x_2339_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2343_ = l_Lean_stringToMessageData(v___x_2342_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2349_ = l_Lean_stringToMessageData(v___x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2352_ = l_Lean_stringToMessageData(v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2353_, lean_object* v_declHint_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v_env_2358_; uint8_t v___x_2359_; 
v___x_2357_ = lean_st_ref_get(v___y_2355_);
v_env_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc_ref(v_env_2358_);
lean_dec(v___x_2357_);
v___x_2359_ = l_Lean_Name_isAnonymous(v_declHint_2354_);
if (v___x_2359_ == 0)
{
uint8_t v_isExporting_2360_; 
v_isExporting_2360_ = lean_ctor_get_uint8(v_env_2358_, sizeof(void*)*8);
if (v_isExporting_2360_ == 0)
{
lean_object* v___x_2361_; 
lean_dec_ref(v_env_2358_);
lean_dec(v_declHint_2354_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v_msg_2353_);
return v___x_2361_;
}
else
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
lean_inc_ref(v_env_2358_);
v___x_2362_ = l_Lean_Environment_setExporting(v_env_2358_, v___x_2359_);
lean_inc(v_declHint_2354_);
lean_inc_ref(v___x_2362_);
v___x_2363_ = l_Lean_Environment_contains(v___x_2362_, v_declHint_2354_, v_isExporting_2360_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
lean_dec_ref(v___x_2362_);
lean_dec_ref(v_env_2358_);
lean_dec(v_declHint_2354_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_msg_2353_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v_c_2370_; lean_object* v___x_2371_; 
v___x_2365_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2367_ = l_Lean_Options_empty;
v___x_2368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2362_);
lean_ctor_set(v___x_2368_, 1, v___x_2365_);
lean_ctor_set(v___x_2368_, 2, v___x_2366_);
lean_ctor_set(v___x_2368_, 3, v___x_2367_);
lean_inc(v_declHint_2354_);
v___x_2369_ = l_Lean_MessageData_ofConstName(v_declHint_2354_, v___x_2359_);
v_c_2370_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2370_, 0, v___x_2368_);
lean_ctor_set(v_c_2370_, 1, v___x_2369_);
v___x_2371_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2358_, v_declHint_2354_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec_ref(v_env_2358_);
lean_dec(v_declHint_2354_);
v___x_2372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v_c_2370_);
v___x_2374_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Lean_MessageData_note(v___x_2375_);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_msg_2353_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2414_; 
v_val_2379_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2381_ = v___x_2371_;
v_isShared_2382_ = v_isSharedCheck_2414_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v___x_2371_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2414_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_mod_2386_; uint8_t v___x_2387_; 
v___x_2383_ = lean_box(0);
v___x_2384_ = l_Lean_Environment_header(v_env_2358_);
lean_dec_ref(v_env_2358_);
v___x_2385_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2384_);
v_mod_2386_ = lean_array_get(v___x_2383_, v___x_2385_, v_val_2379_);
lean_dec(v_val_2379_);
lean_dec_ref(v___x_2385_);
v___x_2387_ = l_Lean_isPrivateName(v_declHint_2354_);
lean_dec(v_declHint_2354_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2388_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v_c_2370_);
v___x_2390_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = l_Lean_MessageData_ofName(v_mod_2386_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Lean_MessageData_note(v___x_2395_);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v_msg_2353_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2397_);
v___x_2399_ = v___x_2381_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2401_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v_c_2370_);
v___x_2403_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = l_Lean_MessageData_ofName(v_mod_2386_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = l_Lean_MessageData_note(v___x_2408_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v_msg_2353_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2410_);
v___x_2412_ = v___x_2381_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2415_; 
lean_dec_ref(v_env_2358_);
lean_dec(v_declHint_2354_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_msg_2353_);
return v___x_2415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2416_, lean_object* v_declHint_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2416_, v_declHint_2417_, v___y_2418_);
lean_dec(v___y_2418_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2421_, lean_object* v_declHint_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2439_; 
v___x_2429_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2421_, v_declHint_2422_, v___y_2427_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2439_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2439_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2434_ = l_Lean_unknownIdentifierMessageTag;
v___x_2435_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v_a_2430_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2435_);
v___x_2437_ = v___x_2432_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2440_, lean_object* v_declHint_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2440_, v_declHint_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_ref_2455_; lean_object* v___x_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2465_; 
v_ref_2455_ = lean_ctor_get(v___y_2452_, 5);
v___x_2456_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_inc(v_ref_2455_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_ref_2455_);
lean_ctor_set(v___x_2461_, 1, v_a_2457_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set_tag(v___x_2459_, 1);
lean_ctor_set(v___x_2459_, 0, v___x_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2473_, lean_object* v_msg_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_fileName_2481_; lean_object* v_fileMap_2482_; lean_object* v_options_2483_; lean_object* v_currRecDepth_2484_; lean_object* v_maxRecDepth_2485_; lean_object* v_ref_2486_; lean_object* v_currNamespace_2487_; lean_object* v_openDecls_2488_; lean_object* v_initHeartbeats_2489_; lean_object* v_maxHeartbeats_2490_; lean_object* v_quotContext_2491_; lean_object* v_currMacroScope_2492_; uint8_t v_diag_2493_; lean_object* v_cancelTk_x3f_2494_; uint8_t v_suppressElabErrors_2495_; lean_object* v_inheritedTraceOptions_2496_; lean_object* v_ref_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_fileName_2481_ = lean_ctor_get(v___y_2478_, 0);
v_fileMap_2482_ = lean_ctor_get(v___y_2478_, 1);
v_options_2483_ = lean_ctor_get(v___y_2478_, 2);
v_currRecDepth_2484_ = lean_ctor_get(v___y_2478_, 3);
v_maxRecDepth_2485_ = lean_ctor_get(v___y_2478_, 4);
v_ref_2486_ = lean_ctor_get(v___y_2478_, 5);
v_currNamespace_2487_ = lean_ctor_get(v___y_2478_, 6);
v_openDecls_2488_ = lean_ctor_get(v___y_2478_, 7);
v_initHeartbeats_2489_ = lean_ctor_get(v___y_2478_, 8);
v_maxHeartbeats_2490_ = lean_ctor_get(v___y_2478_, 9);
v_quotContext_2491_ = lean_ctor_get(v___y_2478_, 10);
v_currMacroScope_2492_ = lean_ctor_get(v___y_2478_, 11);
v_diag_2493_ = lean_ctor_get_uint8(v___y_2478_, sizeof(void*)*14);
v_cancelTk_x3f_2494_ = lean_ctor_get(v___y_2478_, 12);
v_suppressElabErrors_2495_ = lean_ctor_get_uint8(v___y_2478_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2496_ = lean_ctor_get(v___y_2478_, 13);
v_ref_2497_ = l_Lean_replaceRef(v_ref_2473_, v_ref_2486_);
lean_inc_ref(v_inheritedTraceOptions_2496_);
lean_inc(v_cancelTk_x3f_2494_);
lean_inc(v_currMacroScope_2492_);
lean_inc(v_quotContext_2491_);
lean_inc(v_maxHeartbeats_2490_);
lean_inc(v_initHeartbeats_2489_);
lean_inc(v_openDecls_2488_);
lean_inc(v_currNamespace_2487_);
lean_inc(v_maxRecDepth_2485_);
lean_inc(v_currRecDepth_2484_);
lean_inc_ref(v_options_2483_);
lean_inc_ref(v_fileMap_2482_);
lean_inc_ref(v_fileName_2481_);
v___x_2498_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2498_, 0, v_fileName_2481_);
lean_ctor_set(v___x_2498_, 1, v_fileMap_2482_);
lean_ctor_set(v___x_2498_, 2, v_options_2483_);
lean_ctor_set(v___x_2498_, 3, v_currRecDepth_2484_);
lean_ctor_set(v___x_2498_, 4, v_maxRecDepth_2485_);
lean_ctor_set(v___x_2498_, 5, v_ref_2497_);
lean_ctor_set(v___x_2498_, 6, v_currNamespace_2487_);
lean_ctor_set(v___x_2498_, 7, v_openDecls_2488_);
lean_ctor_set(v___x_2498_, 8, v_initHeartbeats_2489_);
lean_ctor_set(v___x_2498_, 9, v_maxHeartbeats_2490_);
lean_ctor_set(v___x_2498_, 10, v_quotContext_2491_);
lean_ctor_set(v___x_2498_, 11, v_currMacroScope_2492_);
lean_ctor_set(v___x_2498_, 12, v_cancelTk_x3f_2494_);
lean_ctor_set(v___x_2498_, 13, v_inheritedTraceOptions_2496_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*14, v_diag_2493_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*14 + 1, v_suppressElabErrors_2495_);
v___x_2499_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2474_, v___y_2476_, v___y_2477_, v___x_2498_, v___y_2479_);
lean_dec_ref_known(v___x_2498_, 14);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2500_, lean_object* v_msg_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2500_, v_msg_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec(v_ref_2500_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2509_, lean_object* v_msg_2510_, lean_object* v_declHint_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v_a_2519_; lean_object* v___x_2520_; 
v___x_2518_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2510_, v_declHint_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2509_, v_a_2519_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2521_, lean_object* v_msg_2522_, lean_object* v_declHint_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2521_, v_msg_2522_, v_declHint_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec(v_ref_2521_);
return v_res_2530_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2533_ = l_Lean_stringToMessageData(v___x_2532_);
return v___x_2533_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2536_ = l_Lean_stringToMessageData(v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2537_, lean_object* v_constName_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2545_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2546_ = 0;
lean_inc(v_constName_2538_);
v___x_2547_ = l_Lean_MessageData_ofConstName(v_constName_2538_, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2545_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2537_, v___x_2550_, v_constName_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2552_, lean_object* v_constName_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2552_, v_constName_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec(v_ref_2552_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_ref_2568_; lean_object* v___x_2569_; 
v_ref_2568_ = lean_ctor_get(v___y_2565_, 5);
v___x_2569_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2568_, v_constName_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; lean_object* v_env_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2585_ = lean_st_ref_get(v___y_2583_);
v_env_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc_ref(v_env_2586_);
lean_dec(v___x_2585_);
v___x_2587_ = 0;
lean_inc(v_constName_2578_);
v___x_2588_ = l_Lean_Environment_find_x3f(v_env_2586_, v_constName_2578_, v___x_2587_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2589_;
}
else
{
lean_object* v_val_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_constName_2578_);
v_val_2590_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2588_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_val_2590_);
lean_dec(v___x_2588_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set_tag(v___x_2592_, 0);
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_val_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
return v_res_2605_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2610_ = lean_unsigned_to_nat(53u);
v___x_2611_ = lean_unsigned_to_nat(62u);
v___x_2612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2614_ = l_mkPanicMessageWithDecl(v___x_2613_, v___x_2612_, v___x_2611_, v___x_2610_, v___x_2609_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2615_, size_t v_i_2616_, lean_object* v_bs_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = lean_usize_dec_lt(v_i_2616_, v_sz_2615_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_bs_2617_);
return v___x_2625_;
}
else
{
lean_object* v_v_2626_; lean_object* v___x_2627_; 
v_v_2626_ = lean_array_uget_borrowed(v_bs_2617_, v_i_2616_);
lean_inc(v_v_2626_);
v___x_2627_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2626_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; lean_object* v_bs_x27_2630_; lean_object* v_a_2632_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = lean_unsigned_to_nat(0u);
v_bs_x27_2630_ = lean_array_uset(v_bs_2617_, v_i_2616_, v___x_2629_);
if (lean_obj_tag(v_a_2628_) == 6)
{
lean_object* v_val_2637_; lean_object* v_numFields_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; 
v_val_2637_ = lean_ctor_get(v_a_2628_, 0);
lean_inc_ref(v_val_2637_);
lean_dec_ref_known(v_a_2628_, 1);
v_numFields_2638_ = lean_ctor_get(v_val_2637_, 4);
lean_inc(v_numFields_2638_);
lean_dec_ref(v_val_2637_);
v___x_2639_ = 0;
v___x_2640_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2640_, 0, v_numFields_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2629_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*2, v___x_2639_);
v_a_2632_ = v___x_2640_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec(v_a_2628_);
v___x_2641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2642_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2641_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v_a_2632_ = v_a_2643_;
goto v___jp_2631_;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v_bs_x27_2630_);
v_a_2644_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2642_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2642_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
v___jp_2631_:
{
size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = ((size_t)1ULL);
v___x_2634_ = lean_usize_add(v_i_2616_, v___x_2633_);
v___x_2635_ = lean_array_uset(v_bs_x27_2630_, v_i_2616_, v_a_2632_);
v_i_2616_ = v___x_2634_;
v_bs_2617_ = v___x_2635_;
goto _start;
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec_ref(v_bs_2617_);
v_a_2652_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2627_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2627_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2660_, lean_object* v_i_2661_, lean_object* v_bs_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
size_t v_sz_boxed_2669_; size_t v_i_boxed_2670_; lean_object* v_res_2671_; 
v_sz_boxed_2669_ = lean_unbox_usize(v_sz_2660_);
lean_dec(v_sz_2660_);
v_i_boxed_2670_ = lean_unbox_usize(v_i_2661_);
lean_dec(v_i_2661_);
v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2669_, v_i_boxed_2670_, v_bs_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
return v_res_2671_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_unsigned_to_nat(16u);
v___x_2674_ = lean_mk_array(v___x_2673_, v___x_2672_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___x_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2680_, uint8_t v_alsoCasesOn_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
uint8_t v___x_2691_; 
v___x_2691_ = l_Lean_Expr_isApp(v_e_2680_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec_ref(v_e_2680_);
v___x_2692_ = lean_box(0);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
else
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_Expr_getAppFn(v_e_2680_);
if (lean_obj_tag(v___x_2694_) == 4)
{
lean_object* v_declName_2695_; lean_object* v_us_2696_; lean_object* v___x_2697_; lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2851_; 
v_declName_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc_n(v_declName_2695_, 2);
v_us_2696_ = lean_ctor_get(v___x_2694_, 1);
lean_inc(v_us_2696_);
lean_dec_ref_known(v___x_2694_, 2);
v___x_2697_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2695_, v___y_2686_);
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2851_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2851_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_2698_) == 1)
{
lean_object* v_val_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2744_; 
v_val_2703_ = lean_ctor_get(v_a_2698_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_a_2698_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2705_ = v_a_2698_;
v_isShared_2706_ = v_isSharedCheck_2744_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_val_2703_);
lean_dec(v_a_2698_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2744_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_dummy_2707_; lean_object* v_nargs_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v_args_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v_dummy_2707_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2708_ = l_Lean_Expr_getAppNumArgs(v_e_2680_);
lean_inc(v_nargs_2708_);
v___x_2709_ = lean_mk_array(v_nargs_2708_, v_dummy_2707_);
v___x_2710_ = lean_unsigned_to_nat(1u);
v___x_2711_ = lean_nat_sub(v_nargs_2708_, v___x_2710_);
lean_dec(v_nargs_2708_);
v_args_2712_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2680_, v___x_2709_, v___x_2711_);
v___x_2713_ = lean_array_get_size(v_args_2712_);
v___x_2714_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2703_);
v___x_2715_ = lean_nat_dec_lt(v___x_2713_, v___x_2714_);
lean_dec(v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v_numParams_2716_; lean_object* v_numDiscrs_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v_numParams_2716_ = lean_ctor_get(v_val_2703_, 0);
v_numDiscrs_2717_ = lean_ctor_get(v_val_2703_, 1);
v___x_2718_ = lean_array_mk(v_us_2696_);
v___x_2719_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2716_);
v___x_2720_ = l_Array_extract___redArg(v_args_2712_, v___x_2719_, v_numParams_2716_);
v___x_2721_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2703_);
v___x_2722_ = lean_array_get(v___x_2702_, v_args_2712_, v___x_2721_);
lean_dec(v___x_2721_);
v___x_2723_ = lean_nat_add(v_numParams_2716_, v___x_2710_);
v___x_2724_ = lean_nat_add(v___x_2723_, v_numDiscrs_2717_);
lean_inc(v___x_2724_);
lean_inc_ref_n(v_args_2712_, 2);
v___x_2725_ = l_Array_toSubarray___redArg(v_args_2712_, v___x_2723_, v___x_2724_);
v___x_2726_ = l_Subarray_copy___redArg(v___x_2725_);
v___x_2727_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2703_);
v___x_2728_ = lean_nat_add(v___x_2724_, v___x_2727_);
lean_dec(v___x_2727_);
lean_inc(v___x_2728_);
v___x_2729_ = l_Array_toSubarray___redArg(v_args_2712_, v___x_2724_, v___x_2728_);
v___x_2730_ = l_Subarray_copy___redArg(v___x_2729_);
v___x_2731_ = l_Array_toSubarray___redArg(v_args_2712_, v___x_2728_, v___x_2713_);
v___x_2732_ = l_Subarray_copy___redArg(v___x_2731_);
v___x_2733_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2733_, 0, v_val_2703_);
lean_ctor_set(v___x_2733_, 1, v_declName_2695_);
lean_ctor_set(v___x_2733_, 2, v___x_2718_);
lean_ctor_set(v___x_2733_, 3, v___x_2720_);
lean_ctor_set(v___x_2733_, 4, v___x_2722_);
lean_ctor_set(v___x_2733_, 5, v___x_2726_);
lean_ctor_set(v___x_2733_, 6, v___x_2730_);
lean_ctor_set(v___x_2733_, 7, v___x_2732_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2733_);
v___x_2735_ = v___x_2705_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2735_);
v___x_2737_ = v___x_2700_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
lean_dec_ref(v_args_2712_);
lean_del_object(v___x_2705_);
lean_dec(v_val_2703_);
lean_dec(v_us_2696_);
lean_dec(v_declName_2695_);
v___x_2740_ = lean_box(0);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2740_);
v___x_2742_ = v___x_2700_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
else
{
lean_object* v___x_2745_; 
lean_del_object(v___x_2700_);
lean_dec(v_a_2698_);
v___x_2745_ = lean_st_ref_get(v___y_2686_);
if (v_alsoCasesOn_2681_ == 0)
{
lean_dec(v___x_2745_);
lean_dec(v_us_2696_);
lean_dec(v_declName_2695_);
lean_dec_ref(v_e_2680_);
goto v___jp_2688_;
}
else
{
lean_object* v_env_2746_; uint8_t v___x_2747_; 
v_env_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc_ref(v_env_2746_);
lean_dec(v___x_2745_);
lean_inc(v_declName_2695_);
v___x_2747_ = l_Lean_isCasesOnRecursor(v_env_2746_, v_declName_2695_);
if (v___x_2747_ == 0)
{
lean_dec(v_us_2696_);
lean_dec(v_declName_2695_);
lean_dec_ref(v_e_2680_);
goto v___jp_2688_;
}
else
{
lean_object* v_indName_2748_; lean_object* v___x_2749_; 
v_indName_2748_ = l_Lean_Name_getPrefix(v_declName_2695_);
v___x_2749_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2748_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2842_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2842_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2842_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
if (lean_obj_tag(v_a_2750_) == 5)
{
lean_object* v_val_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2837_; 
v_val_2754_ = lean_ctor_get(v_a_2750_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_a_2750_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2756_ = v_a_2750_;
v_isShared_2757_ = v_isSharedCheck_2837_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_val_2754_);
lean_dec(v_a_2750_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2837_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v_toConstantVal_2758_; lean_object* v_numParams_2759_; lean_object* v_numIndices_2760_; lean_object* v_ctors_2761_; lean_object* v_nargs_2762_; lean_object* v_dummy_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v_args_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v_toConstantVal_2758_ = lean_ctor_get(v_val_2754_, 0);
lean_inc_ref(v_toConstantVal_2758_);
v_numParams_2759_ = lean_ctor_get(v_val_2754_, 1);
lean_inc(v_numParams_2759_);
v_numIndices_2760_ = lean_ctor_get(v_val_2754_, 2);
lean_inc(v_numIndices_2760_);
v_ctors_2761_ = lean_ctor_get(v_val_2754_, 4);
lean_inc(v_ctors_2761_);
v_nargs_2762_ = l_Lean_Expr_getAppNumArgs(v_e_2680_);
v_dummy_2763_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2762_);
v___x_2764_ = lean_mk_array(v_nargs_2762_, v_dummy_2763_);
v___x_2765_ = lean_unsigned_to_nat(1u);
v___x_2766_ = lean_nat_sub(v_nargs_2762_, v___x_2765_);
lean_dec(v_nargs_2762_);
v_args_2767_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2680_, v___x_2764_, v___x_2766_);
v___x_2768_ = lean_nat_add(v_numParams_2759_, v___x_2765_);
v___x_2769_ = lean_nat_add(v___x_2768_, v_numIndices_2760_);
v___x_2770_ = lean_nat_add(v___x_2769_, v___x_2765_);
lean_dec(v___x_2769_);
v___x_2771_ = l_Lean_InductiveVal_numCtors(v_val_2754_);
lean_dec_ref(v_val_2754_);
v___x_2772_ = lean_nat_add(v___x_2770_, v___x_2771_);
lean_dec(v___x_2771_);
v___x_2773_ = lean_array_get_size(v_args_2767_);
v___x_2774_ = lean_nat_dec_le(v___x_2772_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
lean_dec(v___x_2772_);
lean_dec(v___x_2770_);
lean_dec(v___x_2768_);
lean_dec_ref(v_args_2767_);
lean_dec(v_ctors_2761_);
lean_dec(v_numIndices_2760_);
lean_dec(v_numParams_2759_);
lean_dec_ref(v_toConstantVal_2758_);
lean_del_object(v___x_2756_);
lean_dec(v_us_2696_);
lean_dec(v_declName_2695_);
v___x_2775_ = lean_box(0);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2775_);
v___x_2777_ = v___x_2752_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
else
{
lean_object* v___x_2779_; lean_object* v_params_2780_; lean_object* v_motive_2781_; lean_object* v_discrs_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v_discrInfos_2785_; lean_object* v_alts_2786_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v_lower_2828_; lean_object* v_upper_2829_; uint8_t v___x_2836_; 
lean_del_object(v___x_2752_);
v___x_2779_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2759_);
lean_inc_ref_n(v_args_2767_, 3);
v_params_2780_ = l_Array_toSubarray___redArg(v_args_2767_, v___x_2779_, v_numParams_2759_);
v_motive_2781_ = lean_array_get(v___x_2702_, v_args_2767_, v_numParams_2759_);
lean_dec(v_numParams_2759_);
lean_inc(v___x_2770_);
v_discrs_2782_ = l_Array_toSubarray___redArg(v_args_2767_, v___x_2768_, v___x_2770_);
v___x_2783_ = lean_nat_add(v_numIndices_2760_, v___x_2765_);
lean_dec(v_numIndices_2760_);
v___x_2784_ = lean_box(0);
v_discrInfos_2785_ = lean_mk_array(v___x_2783_, v___x_2784_);
lean_inc(v___x_2772_);
v_alts_2786_ = l_Array_toSubarray___redArg(v_args_2767_, v___x_2770_, v___x_2772_);
v___x_2836_ = lean_nat_dec_le(v___x_2772_, v___x_2779_);
if (v___x_2836_ == 0)
{
v_lower_2828_ = v___x_2772_;
v_upper_2829_ = v___x_2773_;
goto v___jp_2827_;
}
else
{
lean_dec(v___x_2772_);
v_lower_2828_ = v___x_2779_;
v_upper_2829_ = v___x_2773_;
goto v___jp_2827_;
}
v___jp_2787_:
{
lean_object* v___x_2790_; size_t v_sz_2791_; size_t v___x_2792_; lean_object* v___x_2793_; 
v___x_2790_ = lean_array_mk(v_ctors_2761_);
v_sz_2791_ = lean_array_size(v___x_2790_);
v___x_2792_ = ((size_t)0ULL);
v___x_2793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2791_, v___x_2792_, v___x_2790_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2818_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2818_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2818_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v_start_2798_; lean_object* v_stop_2799_; lean_object* v_start_2800_; lean_object* v_stop_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v_start_2798_ = lean_ctor_get(v_params_2780_, 1);
lean_inc(v_start_2798_);
v_stop_2799_ = lean_ctor_get(v_params_2780_, 2);
lean_inc(v_stop_2799_);
v_start_2800_ = lean_ctor_get(v_discrs_2782_, 1);
lean_inc(v_start_2800_);
v_stop_2801_ = lean_ctor_get(v_discrs_2782_, 2);
lean_inc(v_stop_2801_);
v___x_2802_ = lean_nat_sub(v_stop_2799_, v_start_2798_);
lean_dec(v_start_2798_);
lean_dec(v_stop_2799_);
v___x_2803_ = lean_nat_sub(v_stop_2801_, v_start_2800_);
lean_dec(v_start_2800_);
lean_dec(v_stop_2801_);
v___x_2804_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2805_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2802_);
lean_ctor_set(v___x_2805_, 1, v___x_2803_);
lean_ctor_set(v___x_2805_, 2, v_a_2794_);
lean_ctor_set(v___x_2805_, 3, v___y_2789_);
lean_ctor_set(v___x_2805_, 4, v_discrInfos_2785_);
lean_ctor_set(v___x_2805_, 5, v___x_2804_);
v___x_2806_ = lean_array_mk(v_us_2696_);
v___x_2807_ = l_Subarray_copy___redArg(v_params_2780_);
v___x_2808_ = l_Subarray_copy___redArg(v_discrs_2782_);
v___x_2809_ = l_Subarray_copy___redArg(v_alts_2786_);
v___x_2810_ = l_Subarray_copy___redArg(v___y_2788_);
v___x_2811_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2805_);
lean_ctor_set(v___x_2811_, 1, v_declName_2695_);
lean_ctor_set(v___x_2811_, 2, v___x_2806_);
lean_ctor_set(v___x_2811_, 3, v___x_2807_);
lean_ctor_set(v___x_2811_, 4, v_motive_2781_);
lean_ctor_set(v___x_2811_, 5, v___x_2808_);
lean_ctor_set(v___x_2811_, 6, v___x_2809_);
lean_ctor_set(v___x_2811_, 7, v___x_2810_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 1);
lean_ctor_set(v___x_2756_, 0, v___x_2811_);
v___x_2813_ = v___x_2756_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2813_);
v___x_2815_ = v___x_2796_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec_ref(v_alts_2786_);
lean_dec_ref(v_discrInfos_2785_);
lean_dec_ref(v_discrs_2782_);
lean_dec(v_motive_2781_);
lean_dec_ref(v_params_2780_);
lean_del_object(v___x_2756_);
lean_dec(v_us_2696_);
lean_dec(v_declName_2695_);
v_a_2819_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2793_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2793_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
v___jp_2827_:
{
lean_object* v_levelParams_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v_levelParams_2830_ = lean_ctor_get(v_toConstantVal_2758_, 1);
lean_inc(v_levelParams_2830_);
lean_dec_ref(v_toConstantVal_2758_);
v___x_2831_ = l_Array_toSubarray___redArg(v_args_2767_, v_lower_2828_, v_upper_2829_);
v___x_2832_ = l_List_lengthTR___redArg(v_levelParams_2830_);
lean_dec(v_levelParams_2830_);
v___x_2833_ = l_List_lengthTR___redArg(v_us_2696_);
v___x_2834_ = lean_nat_dec_eq(v___x_2832_, v___x_2833_);
lean_dec(v___x_2833_);
lean_dec(v___x_2832_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2788_ = v___x_2831_;
v___y_2789_ = v___x_2835_;
goto v___jp_2787_;
}
else
{
v___y_2788_ = v___x_2831_;
v___y_2789_ = v___x_2784_;
goto v___jp_2787_;
}
}
}
}
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
lean_dec(v_a_2750_);
lean_dec(v_us_2696_);
lean_dec(v_declName_2695_);
lean_dec_ref(v_e_2680_);
v___x_2838_ = lean_box(0);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2838_);
v___x_2840_ = v___x_2752_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_us_2696_);
lean_dec(v_declName_2695_);
lean_dec_ref(v_e_2680_);
v_a_2843_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2749_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2749_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
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
lean_dec_ref(v___x_2694_);
lean_dec_ref(v_e_2680_);
goto v___jp_2688_;
}
}
v___jp_2688_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2852_, lean_object* v_alsoCasesOn_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2860_; lean_object* v_res_2861_; 
v_alsoCasesOn_boxed_2860_ = lean_unbox(v_alsoCasesOn_2853_);
v_res_2861_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2852_, v_alsoCasesOn_boxed_2860_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
if (lean_obj_tag(v_a_2862_) == 0)
{
lean_object* v___x_2864_; 
v___x_2864_ = l_List_reverse___redArg(v_a_2863_);
return v___x_2864_;
}
else
{
lean_object* v_head_2865_; lean_object* v_tail_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2875_; 
v_head_2865_ = lean_ctor_get(v_a_2862_, 0);
v_tail_2866_ = lean_ctor_get(v_a_2862_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2868_ = v_a_2862_;
v_isShared_2869_ = v_isSharedCheck_2875_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_tail_2866_);
lean_inc(v_head_2865_);
lean_dec(v_a_2862_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2875_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = l_Lean_MessageData_ofExpr(v_head_2865_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v_a_2863_);
lean_ctor_set(v___x_2868_, 0, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_a_2863_);
v___x_2872_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
v_a_2862_ = v_tail_2866_;
v_a_2863_ = v___x_2872_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2876_, lean_object* v_x_2877_){
_start:
{
lean_object* v_fnName_2878_; uint8_t v___x_2879_; 
v_fnName_2878_ = lean_ctor_get(v_x_2877_, 0);
v___x_2879_ = l_Lean_Expr_isConstOf(v_x_2876_, v_fnName_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2880_, lean_object* v_x_2881_){
_start:
{
uint8_t v_res_2882_; lean_object* v_r_2883_; 
v_res_2882_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2880_, v_x_2881_);
lean_dec_ref(v_x_2881_);
lean_dec_ref(v_x_2880_);
v_r_2883_ = lean_box(v_res_2882_);
return v_r_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2884_, lean_object* v_type_2885_, lean_object* v_val_2886_, lean_object* v_k_2887_, uint8_t v_nondep_2888_, uint8_t v_kind_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___f_2896_; lean_object* v___x_2897_; 
lean_inc(v___y_2890_);
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2896_, 0, v_k_2887_);
lean_closure_set(v___f_2896_, 1, v___y_2890_);
v___x_2897_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2884_, v_type_2885_, v_val_2886_, v___f_2896_, v_nondep_2888_, v_kind_2889_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2897_) == 0)
{
return v___x_2897_;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2906_, lean_object* v_type_2907_, lean_object* v_val_2908_, lean_object* v_k_2909_, lean_object* v_nondep_2910_, lean_object* v_kind_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
uint8_t v_nondep_boxed_2918_; uint8_t v_kind_boxed_2919_; lean_object* v_res_2920_; 
v_nondep_boxed_2918_ = lean_unbox(v_nondep_2910_);
v_kind_boxed_2919_ = lean_unbox(v_kind_2911_);
v_res_2920_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2906_, v_type_2907_, v_val_2908_, v_k_2909_, v_nondep_boxed_2918_, v_kind_boxed_2919_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2921_, uint8_t v_usedLetOnly_2922_, lean_object* v_x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
lean_inc(v___y_2928_);
lean_inc_ref(v___y_2927_);
lean_inc(v___y_2926_);
lean_inc_ref(v___y_2925_);
lean_inc(v___y_2924_);
lean_inc_ref(v_x_2923_);
v___x_2930_ = lean_apply_7(v_k_2921_, v_x_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, lean_box(0));
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = lean_unsigned_to_nat(1u);
v___x_2933_ = lean_mk_empty_array_with_capacity(v___x_2932_);
v___x_2934_ = lean_array_push(v___x_2933_, v_x_2923_);
v___x_2935_ = 0;
v___x_2936_ = 1;
v___x_2937_ = l_Lean_Meta_mkLetFVars(v___x_2934_, v_a_2931_, v_usedLetOnly_2922_, v___x_2935_, v___x_2936_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec_ref(v___x_2934_);
return v___x_2937_;
}
else
{
lean_dec_ref(v_x_2923_);
return v___x_2930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2938_, lean_object* v_usedLetOnly_2939_, lean_object* v_x_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v_usedLetOnly_boxed_2947_; lean_object* v_res_2948_; 
v_usedLetOnly_boxed_2947_ = lean_unbox(v_usedLetOnly_2939_);
v_res_2948_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2938_, v_usedLetOnly_boxed_2947_, v_x_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2949_, lean_object* v_type_2950_, lean_object* v_val_2951_, lean_object* v_k_2952_, uint8_t v_nondep_2953_, uint8_t v_kind_2954_, uint8_t v_usedLetOnly_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; lean_object* v___f_2963_; lean_object* v___x_2964_; 
v___x_2962_ = lean_box(v_usedLetOnly_2955_);
v___f_2963_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2963_, 0, v_k_2952_);
lean_closure_set(v___f_2963_, 1, v___x_2962_);
v___x_2964_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2949_, v_type_2950_, v_val_2951_, v___f_2963_, v_nondep_2953_, v_kind_2954_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2965_, lean_object* v_type_2966_, lean_object* v_val_2967_, lean_object* v_k_2968_, lean_object* v_nondep_2969_, lean_object* v_kind_2970_, lean_object* v_usedLetOnly_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v_nondep_boxed_2978_; uint8_t v_kind_boxed_2979_; uint8_t v_usedLetOnly_boxed_2980_; lean_object* v_res_2981_; 
v_nondep_boxed_2978_ = lean_unbox(v_nondep_2969_);
v_kind_boxed_2979_ = lean_unbox(v_kind_2970_);
v_usedLetOnly_boxed_2980_ = lean_unbox(v_usedLetOnly_2971_);
v_res_2981_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2965_, v_type_2966_, v_val_2967_, v_k_2968_, v_nondep_boxed_2978_, v_kind_boxed_2979_, v_usedLetOnly_boxed_2980_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_2982_, lean_object* v_positions_2983_, lean_object* v_recFnNames_2984_, lean_object* v_containsRecFn_2985_, lean_object* v_below_2986_, size_t v_sz_2987_, size_t v_i_2988_, lean_object* v_bs_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = lean_usize_dec_lt(v_i_2988_, v_sz_2987_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; 
lean_dec_ref(v_below_2986_);
lean_dec_ref(v_containsRecFn_2985_);
lean_dec_ref(v_recFnNames_2984_);
lean_dec_ref(v_positions_2983_);
lean_dec_ref(v_recArgInfos_2982_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_bs_2989_);
return v___x_2997_;
}
else
{
lean_object* v_v_2998_; lean_object* v___x_2999_; 
v_v_2998_ = lean_array_uget_borrowed(v_bs_2989_, v_i_2988_);
lean_inc_ref(v___y_2993_);
lean_inc(v_v_2998_);
lean_inc_ref(v_below_2986_);
lean_inc_ref(v_containsRecFn_2985_);
lean_inc_ref(v_recFnNames_2984_);
lean_inc_ref(v_positions_2983_);
lean_inc_ref(v_recArgInfos_2982_);
v___x_2999_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_2982_, v_positions_2983_, v_recFnNames_2984_, v_containsRecFn_2985_, v_below_2986_, v_v_2998_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v_bs_x27_3002_; size_t v___x_3003_; size_t v___x_3004_; lean_object* v___x_3005_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = lean_unsigned_to_nat(0u);
v_bs_x27_3002_ = lean_array_uset(v_bs_2989_, v_i_2988_, v___x_3001_);
v___x_3003_ = ((size_t)1ULL);
v___x_3004_ = lean_usize_add(v_i_2988_, v___x_3003_);
v___x_3005_ = lean_array_uset(v_bs_x27_3002_, v_i_2988_, v_a_3000_);
v_i_2988_ = v___x_3004_;
v_bs_2989_ = v___x_3005_;
goto _start;
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec_ref(v_bs_2989_);
lean_dec_ref(v_below_2986_);
lean_dec_ref(v_containsRecFn_2985_);
lean_dec_ref(v_recFnNames_2984_);
lean_dec_ref(v_positions_2983_);
lean_dec_ref(v_recArgInfos_2982_);
v_a_3007_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2999_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2999_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3017_ = l_Lean_stringToMessageData(v___x_3016_);
return v___x_3017_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3020_ = l_Lean_stringToMessageData(v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3021_, lean_object* v_positions_3022_, lean_object* v_recFnNames_3023_, lean_object* v_containsRecFn_3024_, lean_object* v_below_3025_, lean_object* v_e_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
if (lean_obj_tag(v_x_3027_) == 5)
{
lean_object* v_fn_3036_; lean_object* v_arg_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_fn_3036_ = lean_ctor_get(v_x_3027_, 0);
lean_inc_ref(v_fn_3036_);
v_arg_3037_ = lean_ctor_get(v_x_3027_, 1);
lean_inc_ref(v_arg_3037_);
lean_dec_ref_known(v_x_3027_, 2);
v___x_3038_ = lean_array_set(v_x_3028_, v_x_3029_, v_arg_3037_);
v___x_3039_ = lean_unsigned_to_nat(1u);
v___x_3040_ = lean_nat_sub(v_x_3029_, v___x_3039_);
lean_dec(v_x_3029_);
v_x_3027_ = v_fn_3036_;
v_x_3028_ = v___x_3038_;
v_x_3029_ = v___x_3040_;
goto _start;
}
else
{
lean_object* v___f_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_dec(v_x_3029_);
lean_inc_ref(v_x_3027_);
v___f_3042_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3042_, 0, v_x_3027_);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3042_, v_recArgInfos_3021_, v___x_3043_);
if (lean_obj_tag(v___x_3044_) == 1)
{
lean_object* v_val_3045_; lean_object* v___x_3046_; lean_object* v___y_3048_; lean_object* v_recArgPos_3074_; lean_object* v_indGroupInst_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
lean_dec_ref(v_x_3027_);
v_val_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_val_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = lean_array_fget_borrowed(v_recArgInfos_3021_, v_val_3045_);
v_recArgPos_3074_ = lean_ctor_get(v___x_3046_, 2);
v_indGroupInst_3075_ = lean_ctor_get(v___x_3046_, 4);
v___x_3076_ = lean_array_get_size(v_x_3028_);
v___x_3077_ = lean_nat_dec_lt(v_recArgPos_3074_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec(v_val_3045_);
lean_dec_ref(v_x_3028_);
lean_dec_ref(v_below_3025_);
lean_dec_ref(v_containsRecFn_3024_);
lean_dec_ref(v_recFnNames_3023_);
lean_dec_ref(v_positions_3022_);
lean_dec_ref(v_recArgInfos_3021_);
v___x_3078_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3079_ = l_Lean_indentExpr(v_e_3026_);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3080_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_array_fget_borrowed(v_x_3028_, v_recArgPos_3074_);
lean_inc_ref(v___y_3033_);
lean_inc(v___x_3082_);
lean_inc_ref(v_below_3025_);
lean_inc_ref(v_containsRecFn_3024_);
lean_inc_ref(v_recFnNames_3023_);
lean_inc_ref(v_positions_3022_);
lean_inc_ref(v_recArgInfos_3021_);
v___x_3083_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3021_, v_positions_3022_, v_recFnNames_3023_, v_containsRecFn_3024_, v_below_3025_, v___x_3082_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_params_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v_params_3085_ = lean_ctor_get(v_indGroupInst_3075_, 2);
v___x_3086_ = lean_array_get_size(v_params_3085_);
lean_inc_ref(v_positions_3022_);
lean_inc_ref(v_below_3025_);
v___x_3087_ = l_Lean_Elab_Structural_toBelow(v_below_3025_, v___x_3086_, v_positions_3022_, v_val_3045_, v_a_3084_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_dec_ref(v_e_3026_);
v___y_3048_ = v___x_3087_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3088_; uint8_t v___y_3090_; uint8_t v___x_3095_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
v___x_3095_ = l_Lean_Exception_isInterrupt(v_a_3088_);
if (v___x_3095_ == 0)
{
uint8_t v___x_3096_; 
v___x_3096_ = l_Lean_Exception_isRuntime(v_a_3088_);
v___y_3090_ = v___x_3096_;
goto v___jp_3089_;
}
else
{
lean_dec(v_a_3088_);
v___y_3090_ = v___x_3095_;
goto v___jp_3089_;
}
v___jp_3089_:
{
if (v___y_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref_known(v___x_3087_, 1);
v___x_3091_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3092_ = l_Lean_indentExpr(v_e_3026_);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3093_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
v___y_3048_ = v___x_3094_;
goto v___jp_3047_;
}
else
{
lean_dec_ref(v_e_3026_);
v___y_3048_ = v___x_3087_;
goto v___jp_3047_;
}
}
}
}
else
{
lean_dec(v_val_3045_);
lean_dec_ref(v_x_3028_);
lean_dec_ref(v_e_3026_);
lean_dec_ref(v_below_3025_);
lean_dec_ref(v_containsRecFn_3024_);
lean_dec_ref(v_recFnNames_3023_);
lean_dec_ref(v_positions_3022_);
lean_dec_ref(v_recArgInfos_3021_);
return v___x_3083_;
}
}
v___jp_3047_:
{
if (lean_obj_tag(v___y_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v_fixedParamPerm_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_snd_3053_; size_t v_sz_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v_a_3049_ = lean_ctor_get(v___y_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___y_3048_, 1);
v_fixedParamPerm_3050_ = lean_ctor_get(v___x_3046_, 1);
v___x_3051_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3050_, v_x_3028_);
lean_dec_ref(v_x_3028_);
lean_inc(v___x_3046_);
v___x_3052_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3046_, v___x_3051_);
v_snd_3053_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_snd_3053_);
lean_dec_ref(v___x_3052_);
v_sz_3054_ = lean_array_size(v_snd_3053_);
v___x_3055_ = ((size_t)0ULL);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3021_, v_positions_3022_, v_recFnNames_3023_, v_containsRecFn_3024_, v_below_3025_, v_sz_3054_, v___x_3055_, v_snd_3053_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3065_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3061_ = l_Lean_mkAppN(v_a_3049_, v_a_3057_);
lean_dec(v_a_3057_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3061_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v_a_3049_);
v_a_3066_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3056_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3056_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_dec_ref(v_x_3028_);
lean_dec_ref(v_below_3025_);
lean_dec_ref(v_containsRecFn_3024_);
lean_dec_ref(v_recFnNames_3023_);
lean_dec_ref(v_positions_3022_);
lean_dec_ref(v_recArgInfos_3021_);
return v___y_3048_;
}
}
}
else
{
lean_object* v___x_3097_; 
lean_dec(v___x_3044_);
lean_dec_ref(v_e_3026_);
lean_inc_ref(v___y_3033_);
lean_inc_ref(v_below_3025_);
lean_inc_ref(v_containsRecFn_3024_);
lean_inc_ref(v_recFnNames_3023_);
lean_inc_ref(v_positions_3022_);
lean_inc_ref(v_recArgInfos_3021_);
v___x_3097_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3021_, v_positions_3022_, v_recFnNames_3023_, v_containsRecFn_3024_, v_below_3025_, v_x_3027_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; size_t v_sz_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v_sz_3099_ = lean_array_size(v_x_3028_);
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3021_, v_positions_3022_, v_recFnNames_3023_, v_containsRecFn_3024_, v_below_3025_, v_sz_3099_, v___x_3100_, v_x_3028_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3110_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3110_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3110_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = l_Lean_mkAppN(v_a_3098_, v_a_3102_);
lean_dec(v_a_3102_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3106_);
v___x_3108_ = v___x_3104_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec(v_a_3098_);
v_a_3111_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3101_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3101_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_dec_ref(v_x_3028_);
lean_dec_ref(v_below_3025_);
lean_dec_ref(v_containsRecFn_3024_);
lean_dec_ref(v_recFnNames_3023_);
lean_dec_ref(v_positions_3022_);
lean_dec_ref(v_recArgInfos_3021_);
return v___x_3097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3119_, lean_object* v_recArgInfos_3120_, lean_object* v_positions_3121_, lean_object* v_recFnNames_3122_, lean_object* v_containsRecFn_3123_, lean_object* v_below_3124_, uint8_t v___x_3125_, uint8_t v_a_3126_, lean_object* v_x_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_expr_instantiate1(v_body_3119_, v_x_3127_);
lean_inc_ref(v___y_3131_);
v___x_3135_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3120_, v_positions_3121_, v_recFnNames_3122_, v_containsRecFn_3123_, v_below_3124_, v___x_3134_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3135_, 1);
v___x_3137_ = lean_unsigned_to_nat(1u);
v___x_3138_ = lean_mk_empty_array_with_capacity(v___x_3137_);
v___x_3139_ = lean_array_push(v___x_3138_, v_x_3127_);
v___x_3140_ = 1;
v___x_3141_ = l_Lean_Meta_mkLambdaFVars(v___x_3139_, v_a_3136_, v___x_3125_, v_a_3126_, v___x_3125_, v_a_3126_, v___x_3140_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec_ref(v___x_3139_);
return v___x_3141_;
}
else
{
lean_dec_ref(v_x_3127_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3142_, lean_object* v_recArgInfos_3143_, lean_object* v_positions_3144_, lean_object* v_recFnNames_3145_, lean_object* v_containsRecFn_3146_, lean_object* v_below_3147_, lean_object* v___x_3148_, lean_object* v_a_3149_, lean_object* v_x_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
uint8_t v___x_29009__boxed_3157_; uint8_t v_a_29010__boxed_3158_; lean_object* v_res_3159_; 
v___x_29009__boxed_3157_ = lean_unbox(v___x_3148_);
v_a_29010__boxed_3158_ = lean_unbox(v_a_3149_);
v_res_3159_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3142_, v_recArgInfos_3143_, v_positions_3144_, v_recFnNames_3145_, v_containsRecFn_3146_, v_below_3147_, v___x_29009__boxed_3157_, v_a_29010__boxed_3158_, v_x_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v_body_3142_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3160_, lean_object* v_recArgInfos_3161_, lean_object* v_positions_3162_, lean_object* v_recFnNames_3163_, lean_object* v_containsRecFn_3164_, lean_object* v_below_3165_, uint8_t v___x_3166_, uint8_t v_a_3167_, lean_object* v_x_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_expr_instantiate1(v_body_3160_, v_x_3168_);
lean_inc_ref(v___y_3172_);
v___x_3176_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3161_, v_positions_3162_, v_recFnNames_3163_, v_containsRecFn_3164_, v_below_3165_, v___x_3175_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; lean_object* v___x_3182_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
v___x_3178_ = lean_unsigned_to_nat(1u);
v___x_3179_ = lean_mk_empty_array_with_capacity(v___x_3178_);
v___x_3180_ = lean_array_push(v___x_3179_, v_x_3168_);
v___x_3181_ = 1;
v___x_3182_ = l_Lean_Meta_mkForallFVars(v___x_3180_, v_a_3177_, v___x_3166_, v_a_3167_, v_a_3167_, v___x_3181_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec_ref(v___x_3180_);
return v___x_3182_;
}
else
{
lean_dec_ref(v_x_3168_);
return v___x_3176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3183_, lean_object* v_recArgInfos_3184_, lean_object* v_positions_3185_, lean_object* v_recFnNames_3186_, lean_object* v_containsRecFn_3187_, lean_object* v_below_3188_, lean_object* v___x_3189_, lean_object* v_a_3190_, lean_object* v_x_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
uint8_t v___x_29027__boxed_3198_; uint8_t v_a_29028__boxed_3199_; lean_object* v_res_3200_; 
v___x_29027__boxed_3198_ = lean_unbox(v___x_3189_);
v_a_29028__boxed_3199_ = lean_unbox(v_a_3190_);
v_res_3200_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3183_, v_recArgInfos_3184_, v_positions_3185_, v_recFnNames_3186_, v_containsRecFn_3187_, v_below_3188_, v___x_29027__boxed_3198_, v_a_29028__boxed_3199_, v_x_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v_body_3183_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3201_, lean_object* v_recArgInfos_3202_, lean_object* v_positions_3203_, lean_object* v_recFnNames_3204_, lean_object* v_containsRecFn_3205_, lean_object* v_below_3206_, lean_object* v_x_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3201_, v_recArgInfos_3202_, v_positions_3203_, v_recFnNames_3204_, v_containsRecFn_3205_, v_below_3206_, v_x_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v_x_3207_);
lean_dec_ref(v_body_3201_);
return v_res_3214_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3219_ = l_Lean_stringToMessageData(v___x_3218_);
return v___x_3219_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3222_ = l_Lean_stringToMessageData(v___x_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v___x_3229_, lean_object* v_b_3230_, lean_object* v_recArgInfos_3231_, lean_object* v_positions_3232_, lean_object* v_recFnNames_3233_, lean_object* v_containsRecFn_3234_, uint8_t v___x_3235_, uint8_t v_a_3236_, lean_object* v___x_3237_, lean_object* v_a_3238_, lean_object* v_e_3239_, lean_object* v___x_3240_, lean_object* v_xs_3241_, lean_object* v_altBody_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v_options_3284_; uint8_t v_hasTrace_3285_; 
v_options_3284_ = lean_ctor_get(v___y_3246_, 2);
v_hasTrace_3285_ = lean_ctor_get_uint8(v_options_3284_, sizeof(void*)*1);
if (v_hasTrace_3285_ == 0)
{
lean_dec(v___x_3240_);
v___y_3261_ = v___y_3243_;
v___y_3262_ = v___y_3244_;
v___y_3263_ = v___y_3245_;
v___y_3264_ = v___y_3246_;
v___y_3265_ = v___y_3247_;
goto v___jp_3260_;
}
else
{
lean_object* v_inheritedTraceOptions_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
v_inheritedTraceOptions_3286_ = lean_ctor_get(v___y_3246_, 13);
v___x_3287_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3240_);
v___x_3288_ = l_Lean_Name_append(v___x_3287_, v___x_3240_);
v___x_3289_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3286_, v_options_3284_, v___x_3288_);
lean_dec(v___x_3288_);
if (v___x_3289_ == 0)
{
lean_dec(v___x_3240_);
v___y_3261_ = v___y_3243_;
v___y_3262_ = v___y_3244_;
v___y_3263_ = v___y_3245_;
v___y_3264_ = v___y_3246_;
v___y_3265_ = v___y_3247_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3290_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3230_);
v___x_3291_ = l_Nat_reprFast(v_b_3230_);
v___x_3292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
v___x_3293_ = l_Lean_MessageData_ofFormat(v___x_3292_);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3290_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
lean_inc_ref(v_xs_3241_);
v___x_3297_ = lean_array_to_list(v_xs_3241_);
v___x_3298_ = lean_box(0);
v___x_3299_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3297_, v___x_3298_);
v___x_3300_ = l_Lean_MessageData_ofList(v___x_3299_);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3296_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3240_, v___x_3301_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_dec_ref_known(v___x_3302_, 1);
v___y_3261_ = v___y_3243_;
v___y_3262_ = v___y_3244_;
v___y_3263_ = v___y_3245_;
v___y_3264_ = v___y_3246_;
v___y_3265_ = v___y_3247_;
goto v___jp_3260_;
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v_altBody_3242_);
lean_dec_ref(v_xs_3241_);
lean_dec_ref(v_e_3239_);
lean_dec_ref(v_a_3238_);
lean_dec_ref(v_containsRecFn_3234_);
lean_dec_ref(v_recFnNames_3233_);
lean_dec_ref(v_positions_3232_);
lean_dec_ref(v_recArgInfos_3231_);
lean_dec(v_b_3230_);
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
v___jp_3249_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_array_get_borrowed(v___x_3229_, v_xs_3241_, v_b_3230_);
lean_dec(v_b_3230_);
lean_inc_ref(v___y_3253_);
lean_inc(v___x_3255_);
v___x_3256_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3231_, v_positions_3232_, v_recFnNames_3233_, v_containsRecFn_3234_, v___x_3255_, v_altBody_3242_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; uint8_t v___x_3258_; lean_object* v___x_3259_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3258_ = 1;
v___x_3259_ = l_Lean_Meta_mkLambdaFVars(v_xs_3241_, v_a_3257_, v___x_3235_, v_a_3236_, v___x_3235_, v_a_3236_, v___x_3258_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec_ref(v_xs_3241_);
return v___x_3259_;
}
else
{
lean_dec_ref(v_xs_3241_);
return v___x_3256_;
}
}
v___jp_3260_:
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = lean_array_get_size(v_xs_3241_);
v___x_3267_ = lean_nat_dec_eq(v___x_3266_, v___x_3237_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec_ref(v_altBody_3242_);
lean_dec_ref(v_xs_3241_);
lean_dec_ref(v_containsRecFn_3234_);
lean_dec_ref(v_recFnNames_3233_);
lean_dec_ref(v_positions_3232_);
lean_dec_ref(v_recArgInfos_3231_);
lean_dec(v_b_3230_);
v___x_3268_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3269_ = l_Lean_indentExpr(v_a_3238_);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = l_Lean_indentExpr(v_e_3239_);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3274_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
else
{
lean_dec_ref(v_e_3239_);
lean_dec_ref(v_a_3238_);
v___y_3250_ = v___y_3261_;
v___y_3251_ = v___y_3262_;
v___y_3252_ = v___y_3263_;
v___y_3253_ = v___y_3264_;
v___y_3254_ = v___y_3265_;
goto v___jp_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v___x_3311_ = _args[0];
lean_object* v_b_3312_ = _args[1];
lean_object* v_recArgInfos_3313_ = _args[2];
lean_object* v_positions_3314_ = _args[3];
lean_object* v_recFnNames_3315_ = _args[4];
lean_object* v_containsRecFn_3316_ = _args[5];
lean_object* v___x_3317_ = _args[6];
lean_object* v_a_3318_ = _args[7];
lean_object* v___x_3319_ = _args[8];
lean_object* v_a_3320_ = _args[9];
lean_object* v_e_3321_ = _args[10];
lean_object* v___x_3322_ = _args[11];
lean_object* v_xs_3323_ = _args[12];
lean_object* v_altBody_3324_ = _args[13];
lean_object* v___y_3325_ = _args[14];
lean_object* v___y_3326_ = _args[15];
lean_object* v___y_3327_ = _args[16];
lean_object* v___y_3328_ = _args[17];
lean_object* v___y_3329_ = _args[18];
lean_object* v___y_3330_ = _args[19];
_start:
{
uint8_t v___x_29103__boxed_3331_; uint8_t v_a_29104__boxed_3332_; lean_object* v_res_3333_; 
v___x_29103__boxed_3331_ = lean_unbox(v___x_3317_);
v_a_29104__boxed_3332_ = lean_unbox(v_a_3318_);
v_res_3333_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3311_, v_b_3312_, v_recArgInfos_3313_, v_positions_3314_, v_recFnNames_3315_, v_containsRecFn_3316_, v___x_29103__boxed_3331_, v_a_29104__boxed_3332_, v___x_3319_, v_a_3320_, v_e_3321_, v___x_3322_, v_xs_3323_, v_altBody_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec(v___x_3319_);
lean_dec_ref(v___x_3311_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3334_, lean_object* v_positions_3335_, lean_object* v_recFnNames_3336_, lean_object* v_containsRecFn_3337_, uint8_t v_a_3338_, lean_object* v_e_3339_, lean_object* v_as_3340_, lean_object* v_bs_3341_, lean_object* v_i_3342_, lean_object* v_cs_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3350_ = lean_array_get_size(v_as_3340_);
v___x_3351_ = lean_nat_dec_lt(v_i_3342_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
lean_dec(v_i_3342_);
lean_dec_ref(v_e_3339_);
lean_dec_ref(v_containsRecFn_3337_);
lean_dec_ref(v_recFnNames_3336_);
lean_dec_ref(v_positions_3335_);
lean_dec_ref(v_recArgInfos_3334_);
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v_cs_3343_);
return v___x_3352_;
}
else
{
lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3353_ = lean_array_get_size(v_bs_3341_);
v___x_3354_ = lean_nat_dec_lt(v_i_3342_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec(v_i_3342_);
lean_dec_ref(v_e_3339_);
lean_dec_ref(v_containsRecFn_3337_);
lean_dec_ref(v_recFnNames_3336_);
lean_dec_ref(v_positions_3335_);
lean_dec_ref(v_recArgInfos_3334_);
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_cs_3343_);
return v___x_3355_;
}
else
{
lean_object* v___x_3356_; uint8_t v___x_3357_; lean_object* v___x_3358_; lean_object* v_a_3359_; lean_object* v_b_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; 
v___x_3356_ = l_Lean_instInhabitedExpr;
v___x_3357_ = 0;
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3359_ = lean_array_fget_borrowed(v_as_3340_, v_i_3342_);
v_b_3360_ = lean_array_fget_borrowed(v_bs_3341_, v_i_3342_);
v___x_3361_ = lean_unsigned_to_nat(1u);
v___x_3362_ = lean_nat_add(v_b_3360_, v___x_3361_);
v___x_3363_ = lean_box(v___x_3357_);
v___x_3364_ = lean_box(v_a_3338_);
lean_inc_ref(v_e_3339_);
lean_inc_n(v_a_3359_, 2);
lean_inc(v___x_3362_);
lean_inc_ref(v_containsRecFn_3337_);
lean_inc_ref(v_recFnNames_3336_);
lean_inc_ref(v_positions_3335_);
lean_inc_ref(v_recArgInfos_3334_);
lean_inc(v_b_3360_);
v___f_3365_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 20, 12);
lean_closure_set(v___f_3365_, 0, v___x_3356_);
lean_closure_set(v___f_3365_, 1, v_b_3360_);
lean_closure_set(v___f_3365_, 2, v_recArgInfos_3334_);
lean_closure_set(v___f_3365_, 3, v_positions_3335_);
lean_closure_set(v___f_3365_, 4, v_recFnNames_3336_);
lean_closure_set(v___f_3365_, 5, v_containsRecFn_3337_);
lean_closure_set(v___f_3365_, 6, v___x_3363_);
lean_closure_set(v___f_3365_, 7, v___x_3364_);
lean_closure_set(v___f_3365_, 8, v___x_3362_);
lean_closure_set(v___f_3365_, 9, v_a_3359_);
lean_closure_set(v___f_3365_, 10, v_e_3339_);
lean_closure_set(v___f_3365_, 11, v___x_3358_);
v___x_3366_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3359_, v___x_3362_, v___f_3365_, v___x_3357_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v___x_3368_ = lean_nat_add(v_i_3342_, v___x_3361_);
lean_dec(v_i_3342_);
v___x_3369_ = lean_array_push(v_cs_3343_, v_a_3367_);
v_i_3342_ = v___x_3368_;
v_cs_3343_ = v___x_3369_;
goto _start;
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v_cs_3343_);
lean_dec(v_i_3342_);
lean_dec_ref(v_e_3339_);
lean_dec_ref(v_containsRecFn_3337_);
lean_dec_ref(v_recFnNames_3336_);
lean_dec_ref(v_positions_3335_);
lean_dec_ref(v_recArgInfos_3334_);
v_a_3371_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3366_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3366_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
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
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3381_ = l_Lean_stringToMessageData(v___x_3380_);
return v___x_3381_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3384_ = l_Lean_stringToMessageData(v___x_3383_);
return v___x_3384_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3388_, lean_object* v_positions_3389_, lean_object* v_recFnNames_3390_, lean_object* v_containsRecFn_3391_, lean_object* v_below_3392_, lean_object* v_e_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v_e_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___x_3413_; 
lean_inc_ref(v_containsRecFn_3391_);
lean_inc(v_a_3398_);
lean_inc_ref(v_a_3397_);
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3395_);
lean_inc(v_a_3394_);
lean_inc_ref(v_e_3393_);
v___x_3413_ = lean_apply_7(v_containsRecFn_3391_, v_e_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, lean_box(0));
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3636_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3636_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3636_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_unbox(v_a_3414_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3420_; 
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v_e_3393_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_e_3393_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
else
{
uint8_t v___x_3422_; 
lean_del_object(v___x_3416_);
v___x_3422_ = 0;
switch(lean_obj_tag(v_e_3393_))
{
case 6:
{
lean_object* v_binderName_3423_; lean_object* v_binderType_3424_; lean_object* v_body_3425_; uint8_t v_binderInfo_3426_; lean_object* v___x_3427_; 
v_binderName_3423_ = lean_ctor_get(v_e_3393_, 0);
lean_inc(v_binderName_3423_);
v_binderType_3424_ = lean_ctor_get(v_e_3393_, 1);
lean_inc_ref(v_binderType_3424_);
v_body_3425_ = lean_ctor_get(v_e_3393_, 2);
lean_inc_ref(v_body_3425_);
v_binderInfo_3426_ = lean_ctor_get_uint8(v_e_3393_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3393_, 3);
lean_inc_ref(v_a_3397_);
lean_inc_ref(v_below_3392_);
lean_inc_ref(v_containsRecFn_3391_);
lean_inc_ref(v_recFnNames_3390_);
lean_inc_ref(v_positions_3389_);
lean_inc_ref(v_recArgInfos_3388_);
v___x_3427_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3388_, v_positions_3389_, v_recFnNames_3390_, v_containsRecFn_3391_, v_below_3392_, v_binderType_3424_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___f_3430_; uint8_t v___x_3431_; lean_object* v___x_3432_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = lean_box(v___x_3422_);
v___f_3430_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3430_, 0, v_body_3425_);
lean_closure_set(v___f_3430_, 1, v_recArgInfos_3388_);
lean_closure_set(v___f_3430_, 2, v_positions_3389_);
lean_closure_set(v___f_3430_, 3, v_recFnNames_3390_);
lean_closure_set(v___f_3430_, 4, v_containsRecFn_3391_);
lean_closure_set(v___f_3430_, 5, v_below_3392_);
lean_closure_set(v___f_3430_, 6, v___x_3429_);
lean_closure_set(v___f_3430_, 7, v_a_3414_);
v___x_3431_ = 0;
v___x_3432_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3423_, v_binderInfo_3426_, v_a_3428_, v___f_3430_, v___x_3431_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec_ref(v_a_3397_);
return v___x_3432_;
}
else
{
lean_dec_ref(v_body_3425_);
lean_dec(v_binderName_3423_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
return v___x_3427_;
}
}
case 7:
{
lean_object* v_binderName_3433_; lean_object* v_binderType_3434_; lean_object* v_body_3435_; uint8_t v_binderInfo_3436_; lean_object* v___x_3437_; 
v_binderName_3433_ = lean_ctor_get(v_e_3393_, 0);
lean_inc(v_binderName_3433_);
v_binderType_3434_ = lean_ctor_get(v_e_3393_, 1);
lean_inc_ref(v_binderType_3434_);
v_body_3435_ = lean_ctor_get(v_e_3393_, 2);
lean_inc_ref(v_body_3435_);
v_binderInfo_3436_ = lean_ctor_get_uint8(v_e_3393_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3393_, 3);
lean_inc_ref(v_a_3397_);
lean_inc_ref(v_below_3392_);
lean_inc_ref(v_containsRecFn_3391_);
lean_inc_ref(v_recFnNames_3390_);
lean_inc_ref(v_positions_3389_);
lean_inc_ref(v_recArgInfos_3388_);
v___x_3437_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3388_, v_positions_3389_, v_recFnNames_3390_, v_containsRecFn_3391_, v_below_3392_, v_binderType_3434_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; lean_object* v___f_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = lean_box(v___x_3422_);
v___f_3440_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3440_, 0, v_body_3435_);
lean_closure_set(v___f_3440_, 1, v_recArgInfos_3388_);
lean_closure_set(v___f_3440_, 2, v_positions_3389_);
lean_closure_set(v___f_3440_, 3, v_recFnNames_3390_);
lean_closure_set(v___f_3440_, 4, v_containsRecFn_3391_);
lean_closure_set(v___f_3440_, 5, v_below_3392_);
lean_closure_set(v___f_3440_, 6, v___x_3439_);
lean_closure_set(v___f_3440_, 7, v_a_3414_);
v___x_3441_ = 0;
v___x_3442_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3433_, v_binderInfo_3436_, v_a_3438_, v___f_3440_, v___x_3441_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec_ref(v_a_3397_);
return v___x_3442_;
}
else
{
lean_dec_ref(v_body_3435_);
lean_dec(v_binderName_3433_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
return v___x_3437_;
}
}
case 8:
{
lean_object* v_declName_3443_; lean_object* v_type_3444_; lean_object* v_value_3445_; lean_object* v_body_3446_; uint8_t v_nondep_3447_; lean_object* v___x_3448_; 
lean_dec(v_a_3414_);
v_declName_3443_ = lean_ctor_get(v_e_3393_, 0);
lean_inc(v_declName_3443_);
v_type_3444_ = lean_ctor_get(v_e_3393_, 1);
lean_inc_ref(v_type_3444_);
v_value_3445_ = lean_ctor_get(v_e_3393_, 2);
lean_inc_ref(v_value_3445_);
v_body_3446_ = lean_ctor_get(v_e_3393_, 3);
lean_inc_ref(v_body_3446_);
v_nondep_3447_ = lean_ctor_get_uint8(v_e_3393_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3393_, 4);
lean_inc_ref(v_a_3397_);
lean_inc_ref(v_below_3392_);
lean_inc_ref(v_containsRecFn_3391_);
lean_inc_ref(v_recFnNames_3390_);
lean_inc_ref(v_positions_3389_);
lean_inc_ref(v_recArgInfos_3388_);
v___x_3448_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3388_, v_positions_3389_, v_recFnNames_3390_, v_containsRecFn_3391_, v_below_3392_, v_type_3444_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3450_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
lean_inc_ref(v_a_3397_);
lean_inc_ref(v_below_3392_);
lean_inc_ref(v_containsRecFn_3391_);
lean_inc_ref(v_recFnNames_3390_);
lean_inc_ref(v_positions_3389_);
lean_inc_ref(v_recArgInfos_3388_);
v___x_3450_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3388_, v_positions_3389_, v_recFnNames_3390_, v_containsRecFn_3391_, v_below_3392_, v_value_3445_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___f_3452_; uint8_t v___x_3453_; lean_object* v___x_3454_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___f_3452_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3452_, 0, v_body_3446_);
lean_closure_set(v___f_3452_, 1, v_recArgInfos_3388_);
lean_closure_set(v___f_3452_, 2, v_positions_3389_);
lean_closure_set(v___f_3452_, 3, v_recFnNames_3390_);
lean_closure_set(v___f_3452_, 4, v_containsRecFn_3391_);
lean_closure_set(v___f_3452_, 5, v_below_3392_);
v___x_3453_ = 0;
v___x_3454_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3443_, v_a_3449_, v_a_3451_, v___f_3452_, v_nondep_3447_, v___x_3453_, v___x_3422_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec_ref(v_a_3397_);
return v___x_3454_;
}
else
{
lean_dec(v_a_3449_);
lean_dec_ref(v_body_3446_);
lean_dec(v_declName_3443_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
return v___x_3450_;
}
}
else
{
lean_dec_ref(v_body_3446_);
lean_dec_ref(v_value_3445_);
lean_dec(v_declName_3443_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
return v___x_3448_;
}
}
case 10:
{
lean_object* v_data_3455_; lean_object* v_expr_3456_; lean_object* v___x_3457_; 
lean_dec(v_a_3414_);
v_data_3455_ = lean_ctor_get(v_e_3393_, 0);
lean_inc(v_data_3455_);
v_expr_3456_ = lean_ctor_get(v_e_3393_, 1);
lean_inc_ref(v_expr_3456_);
v___x_3457_ = l_Lean_getRecAppSyntax_x3f(v_e_3393_);
lean_dec_ref_known(v_e_3393_, 2);
if (lean_obj_tag(v___x_3457_) == 1)
{
lean_object* v_val_3458_; lean_object* v_fileName_3459_; lean_object* v_fileMap_3460_; lean_object* v_options_3461_; lean_object* v_currRecDepth_3462_; lean_object* v_maxRecDepth_3463_; lean_object* v_ref_3464_; lean_object* v_currNamespace_3465_; lean_object* v_openDecls_3466_; lean_object* v_initHeartbeats_3467_; lean_object* v_maxHeartbeats_3468_; lean_object* v_quotContext_3469_; lean_object* v_currMacroScope_3470_; uint8_t v_diag_3471_; lean_object* v_cancelTk_x3f_3472_; uint8_t v_suppressElabErrors_3473_; lean_object* v_inheritedTraceOptions_3474_; lean_object* v_ref_3475_; lean_object* v___x_3476_; 
lean_dec(v_data_3455_);
v_val_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_val_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v_fileName_3459_ = lean_ctor_get(v_a_3397_, 0);
lean_inc_ref(v_fileName_3459_);
v_fileMap_3460_ = lean_ctor_get(v_a_3397_, 1);
lean_inc_ref(v_fileMap_3460_);
v_options_3461_ = lean_ctor_get(v_a_3397_, 2);
lean_inc_ref(v_options_3461_);
v_currRecDepth_3462_ = lean_ctor_get(v_a_3397_, 3);
lean_inc(v_currRecDepth_3462_);
v_maxRecDepth_3463_ = lean_ctor_get(v_a_3397_, 4);
lean_inc(v_maxRecDepth_3463_);
v_ref_3464_ = lean_ctor_get(v_a_3397_, 5);
lean_inc(v_ref_3464_);
v_currNamespace_3465_ = lean_ctor_get(v_a_3397_, 6);
lean_inc(v_currNamespace_3465_);
v_openDecls_3466_ = lean_ctor_get(v_a_3397_, 7);
lean_inc(v_openDecls_3466_);
v_initHeartbeats_3467_ = lean_ctor_get(v_a_3397_, 8);
lean_inc(v_initHeartbeats_3467_);
v_maxHeartbeats_3468_ = lean_ctor_get(v_a_3397_, 9);
lean_inc(v_maxHeartbeats_3468_);
v_quotContext_3469_ = lean_ctor_get(v_a_3397_, 10);
lean_inc(v_quotContext_3469_);
v_currMacroScope_3470_ = lean_ctor_get(v_a_3397_, 11);
lean_inc(v_currMacroScope_3470_);
v_diag_3471_ = lean_ctor_get_uint8(v_a_3397_, sizeof(void*)*14);
v_cancelTk_x3f_3472_ = lean_ctor_get(v_a_3397_, 12);
lean_inc(v_cancelTk_x3f_3472_);
v_suppressElabErrors_3473_ = lean_ctor_get_uint8(v_a_3397_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3474_ = lean_ctor_get(v_a_3397_, 13);
lean_inc_ref(v_inheritedTraceOptions_3474_);
lean_dec_ref(v_a_3397_);
v_ref_3475_ = l_Lean_replaceRef(v_val_3458_, v_ref_3464_);
lean_dec(v_ref_3464_);
lean_dec(v_val_3458_);
v___x_3476_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3476_, 0, v_fileName_3459_);
lean_ctor_set(v___x_3476_, 1, v_fileMap_3460_);
lean_ctor_set(v___x_3476_, 2, v_options_3461_);
lean_ctor_set(v___x_3476_, 3, v_currRecDepth_3462_);
lean_ctor_set(v___x_3476_, 4, v_maxRecDepth_3463_);
lean_ctor_set(v___x_3476_, 5, v_ref_3475_);
lean_ctor_set(v___x_3476_, 6, v_currNamespace_3465_);
lean_ctor_set(v___x_3476_, 7, v_openDecls_3466_);
lean_ctor_set(v___x_3476_, 8, v_initHeartbeats_3467_);
lean_ctor_set(v___x_3476_, 9, v_maxHeartbeats_3468_);
lean_ctor_set(v___x_3476_, 10, v_quotContext_3469_);
lean_ctor_set(v___x_3476_, 11, v_currMacroScope_3470_);
lean_ctor_set(v___x_3476_, 12, v_cancelTk_x3f_3472_);
lean_ctor_set(v___x_3476_, 13, v_inheritedTraceOptions_3474_);
lean_ctor_set_uint8(v___x_3476_, sizeof(void*)*14, v_diag_3471_);
lean_ctor_set_uint8(v___x_3476_, sizeof(void*)*14 + 1, v_suppressElabErrors_3473_);
v_e_3393_ = v_expr_3456_;
v_a_3397_ = v___x_3476_;
goto _start;
}
else
{
lean_object* v___x_3478_; 
lean_dec(v___x_3457_);
v___x_3478_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3388_, v_positions_3389_, v_recFnNames_3390_, v_containsRecFn_3391_, v_below_3392_, v_expr_3456_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3487_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3481_ = v___x_3478_;
v_isShared_3482_ = v_isSharedCheck_3487_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3487_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = l_Lean_mkMData(v_data_3455_, v_a_3479_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3483_);
v___x_3485_ = v___x_3481_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
else
{
lean_dec(v_data_3455_);
return v___x_3478_;
}
}
}
case 11:
{
lean_object* v_typeName_3488_; lean_object* v_idx_3489_; lean_object* v_struct_3490_; lean_object* v___x_3491_; 
lean_dec(v_a_3414_);
v_typeName_3488_ = lean_ctor_get(v_e_3393_, 0);
lean_inc(v_typeName_3488_);
v_idx_3489_ = lean_ctor_get(v_e_3393_, 1);
lean_inc(v_idx_3489_);
v_struct_3490_ = lean_ctor_get(v_e_3393_, 2);
lean_inc_ref(v_struct_3490_);
lean_dec_ref_known(v_e_3393_, 3);
v___x_3491_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3388_, v_positions_3389_, v_recFnNames_3390_, v_containsRecFn_3391_, v_below_3392_, v_struct_3490_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3500_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3496_ = l_Lean_mkProj(v_typeName_3488_, v_idx_3489_, v_a_3492_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3496_);
v___x_3498_ = v___x_3494_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
else
{
lean_dec(v_idx_3489_);
lean_dec(v_typeName_3488_);
return v___x_3491_;
}
}
case 5:
{
uint8_t v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_unbox(v_a_3414_);
lean_inc_ref(v_e_3393_);
v___x_3502_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3393_, v___x_3501_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
if (lean_obj_tag(v_a_3503_) == 0)
{
lean_dec(v_a_3414_);
v_e_3401_ = v_e_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
v___y_3405_ = v_a_3397_;
v___y_3406_ = v_a_3398_;
goto v___jp_3400_;
}
else
{
lean_object* v_val_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v_val_3504_ = lean_ctor_get(v_a_3503_, 0);
lean_inc(v_val_3504_);
lean_dec_ref_known(v_a_3503_, 1);
v___x_3505_ = lean_unsigned_to_nat(0u);
v___x_3506_ = lean_array_get_size(v_recArgInfos_3388_);
v___x_3507_ = lean_nat_dec_lt(v___x_3505_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_dec(v_val_3504_);
lean_dec(v_a_3414_);
v_e_3401_ = v_e_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
v___y_3405_ = v_a_3397_;
v___y_3406_ = v_a_3398_;
goto v___jp_3400_;
}
else
{
if (v___x_3507_ == 0)
{
lean_dec(v_val_3504_);
lean_dec(v_a_3414_);
v_e_3401_ = v_e_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
v___y_3405_ = v_a_3397_;
v___y_3406_ = v_a_3398_;
goto v___jp_3400_;
}
else
{
size_t v___x_3508_; size_t v___x_3509_; uint8_t v___x_3510_; 
v___x_3508_ = ((size_t)0ULL);
v___x_3509_ = lean_usize_of_nat(v___x_3506_);
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3393_, v_recArgInfos_3388_, v___x_3508_, v___x_3509_);
if (v___x_3510_ == 0)
{
lean_dec(v_val_3504_);
lean_dec(v_a_3414_);
v_e_3401_ = v_e_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
v___y_3405_ = v_a_3397_;
v___y_3406_ = v_a_3398_;
goto v___jp_3400_;
}
else
{
lean_object* v_inheritedTraceOptions_3511_; lean_object* v___x_3512_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___x_3582_; 
v_inheritedTraceOptions_3511_ = lean_ctor_get(v_a_3397_, 13);
v___x_3512_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3582_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3512_, v_inheritedTraceOptions_3511_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; uint8_t v___x_3584_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3584_ = lean_unbox(v_a_3583_);
lean_dec(v_a_3583_);
if (v___x_3584_ == 0)
{
v___y_3514_ = v_a_3394_;
v___y_3515_ = v_a_3395_;
v___y_3516_ = v_a_3396_;
v___y_3517_ = v_a_3397_;
v___y_3518_ = v_a_3398_;
goto v___jp_3513_;
}
else
{
lean_object* v___x_3585_; 
lean_inc(v_a_3398_);
lean_inc_ref(v_a_3397_);
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3395_);
lean_inc_ref(v_below_3392_);
v___x_3585_ = lean_infer_type(v_below_3392_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3585_, 1);
v___x_3587_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3392_);
v___x_3588_ = l_Lean_MessageData_ofExpr(v_below_3392_);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3589_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = l_Lean_MessageData_ofExpr(v_a_3586_);
v___x_3593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3591_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3512_, v___x_3593_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_dec_ref_known(v___x_3594_, 1);
v___y_3514_ = v_a_3394_;
v___y_3515_ = v_a_3395_;
v___y_3516_ = v_a_3396_;
v___y_3517_ = v_a_3397_;
v___y_3518_ = v_a_3398_;
goto v___jp_3513_;
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_val_3504_);
lean_dec_ref_known(v_e_3393_, 2);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
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
lean_dec(v_val_3504_);
lean_dec_ref_known(v_e_3393_, 2);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
return v___x_3585_;
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec(v_val_3504_);
lean_dec_ref_known(v_e_3393_, 2);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v_a_3603_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3582_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3582_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
v___jp_3513_:
{
lean_object* v___x_3519_; 
lean_inc_ref(v_below_3392_);
v___x_3519_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3504_, v_below_3392_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
if (lean_obj_tag(v_a_3520_) == 1)
{
lean_object* v_val_3521_; lean_object* v_toMatcherInfo_3522_; lean_object* v_matcherName_3523_; lean_object* v_matcherLevels_3524_; lean_object* v_params_3525_; lean_object* v_motive_3526_; lean_object* v_discrs_3527_; lean_object* v_alts_3528_; lean_object* v_remaining_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; 
lean_dec_ref(v_below_3392_);
v_val_3521_ = lean_ctor_get(v_a_3520_, 0);
lean_inc(v_val_3521_);
lean_dec_ref_known(v_a_3520_, 1);
v_toMatcherInfo_3522_ = lean_ctor_get(v_val_3521_, 0);
lean_inc_ref(v_toMatcherInfo_3522_);
v_matcherName_3523_ = lean_ctor_get(v_val_3521_, 1);
lean_inc(v_matcherName_3523_);
v_matcherLevels_3524_ = lean_ctor_get(v_val_3521_, 2);
lean_inc_ref(v_matcherLevels_3524_);
v_params_3525_ = lean_ctor_get(v_val_3521_, 3);
lean_inc_ref(v_params_3525_);
v_motive_3526_ = lean_ctor_get(v_val_3521_, 4);
lean_inc_ref(v_motive_3526_);
v_discrs_3527_ = lean_ctor_get(v_val_3521_, 5);
lean_inc_ref(v_discrs_3527_);
v_alts_3528_ = lean_ctor_get(v_val_3521_, 6);
lean_inc_ref(v_alts_3528_);
v_remaining_3529_ = lean_ctor_get(v_val_3521_, 7);
lean_inc_ref(v_remaining_3529_);
v___x_3530_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3521_);
v___x_3531_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3532_ = lean_unbox(v_a_3414_);
lean_dec(v_a_3414_);
v___x_3533_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3388_, v_positions_3389_, v_recFnNames_3390_, v_containsRecFn_3391_, v___x_3532_, v_e_3393_, v_alts_3528_, v___x_3530_, v___x_3505_, v___x_3531_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___x_3530_);
lean_dec_ref(v_alts_3528_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3543_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3543_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3543_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3538_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3538_, 0, v_toMatcherInfo_3522_);
lean_ctor_set(v___x_3538_, 1, v_matcherName_3523_);
lean_ctor_set(v___x_3538_, 2, v_matcherLevels_3524_);
lean_ctor_set(v___x_3538_, 3, v_params_3525_);
lean_ctor_set(v___x_3538_, 4, v_motive_3526_);
lean_ctor_set(v___x_3538_, 5, v_discrs_3527_);
lean_ctor_set(v___x_3538_, 6, v_a_3534_);
lean_ctor_set(v___x_3538_, 7, v_remaining_3529_);
v___x_3539_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3538_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3539_);
v___x_3541_ = v___x_3536_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec_ref(v_remaining_3529_);
lean_dec_ref(v_discrs_3527_);
lean_dec_ref(v_motive_3526_);
lean_dec_ref(v_params_3525_);
lean_dec_ref(v_matcherLevels_3524_);
lean_dec(v_matcherName_3523_);
lean_dec_ref(v_toMatcherInfo_3522_);
v_a_3544_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3533_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3533_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3552_; lean_object* v___x_3553_; 
lean_dec(v_a_3520_);
lean_dec(v_a_3414_);
v_inheritedTraceOptions_3552_ = lean_ctor_get(v___y_3517_, 13);
v___x_3553_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3512_, v_inheritedTraceOptions_3552_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; uint8_t v___x_3555_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = lean_unbox(v_a_3554_);
lean_dec(v_a_3554_);
if (v___x_3555_ == 0)
{
v_e_3401_ = v_e_3393_;
v___y_3402_ = v___y_3514_;
v___y_3403_ = v___y_3515_;
v___y_3404_ = v___y_3516_;
v___y_3405_ = v___y_3517_;
v___y_3406_ = v___y_3518_;
goto v___jp_3400_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3557_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3512_, v___x_3556_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_dec_ref_known(v___x_3557_, 1);
v_e_3401_ = v_e_3393_;
v___y_3402_ = v___y_3514_;
v___y_3403_ = v___y_3515_;
v___y_3404_ = v___y_3516_;
v___y_3405_ = v___y_3517_;
v___y_3406_ = v___y_3518_;
goto v___jp_3400_;
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec_ref(v___y_3517_);
lean_dec_ref_known(v_e_3393_, 2);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec_ref(v___y_3517_);
lean_dec_ref_known(v_e_3393_, 2);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v_a_3566_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3553_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3553_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec_ref(v___y_3517_);
lean_dec_ref_known(v_e_3393_, 2);
lean_dec(v_a_3414_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v_a_3574_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3519_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3519_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
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
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref_known(v_e_3393_, 2);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v_a_3611_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3502_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3502_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
default: 
{
lean_object* v___x_3619_; 
lean_dec(v_a_3414_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
lean_inc_ref(v_e_3393_);
v___x_3619_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3390_, v_e_3393_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec_ref(v_a_3397_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v___x_3619_, 0);
lean_dec(v_unused_3627_);
v___x_3621_ = v___x_3619_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_dec(v___x_3619_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v_e_3393_);
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_e_3393_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v_e_3393_);
v_a_3628_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3619_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3619_);
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
}
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec_ref(v_a_3397_);
lean_dec_ref(v_e_3393_);
lean_dec_ref(v_below_3392_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v_a_3637_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3413_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3413_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
v___jp_3400_:
{
lean_object* v_dummy_3407_; lean_object* v_nargs_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_dummy_3407_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3408_ = l_Lean_Expr_getAppNumArgs(v_e_3401_);
lean_inc(v_nargs_3408_);
v___x_3409_ = lean_mk_array(v_nargs_3408_, v_dummy_3407_);
v___x_3410_ = lean_unsigned_to_nat(1u);
v___x_3411_ = lean_nat_sub(v_nargs_3408_, v___x_3410_);
lean_dec(v_nargs_3408_);
lean_inc_ref(v_e_3401_);
v___x_3412_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3388_, v_positions_3389_, v_recFnNames_3390_, v_containsRecFn_3391_, v_below_3392_, v_e_3401_, v_e_3401_, v___x_3409_, v___x_3411_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec_ref(v___y_3405_);
return v___x_3412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3645_, lean_object* v_recArgInfos_3646_, lean_object* v_positions_3647_, lean_object* v_recFnNames_3648_, lean_object* v_containsRecFn_3649_, lean_object* v_below_3650_, lean_object* v_x_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_expr_instantiate1(v_body_3645_, v_x_3651_);
lean_inc_ref(v___y_3655_);
v___x_3659_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3646_, v_positions_3647_, v_recFnNames_3648_, v_containsRecFn_3649_, v_below_3650_, v___x_3658_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3660_, lean_object* v_positions_3661_, lean_object* v_recFnNames_3662_, lean_object* v_containsRecFn_3663_, lean_object* v_below_3664_, lean_object* v_sz_3665_, lean_object* v_i_3666_, lean_object* v_bs_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
size_t v_sz_boxed_3674_; size_t v_i_boxed_3675_; lean_object* v_res_3676_; 
v_sz_boxed_3674_ = lean_unbox_usize(v_sz_3665_);
lean_dec(v_sz_3665_);
v_i_boxed_3675_ = lean_unbox_usize(v_i_3666_);
lean_dec(v_i_3666_);
v_res_3676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3660_, v_positions_3661_, v_recFnNames_3662_, v_containsRecFn_3663_, v_below_3664_, v_sz_boxed_3674_, v_i_boxed_3675_, v_bs_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3677_, lean_object* v_positions_3678_, lean_object* v_recFnNames_3679_, lean_object* v_containsRecFn_3680_, lean_object* v_a_3681_, lean_object* v_e_3682_, lean_object* v_as_3683_, lean_object* v_bs_3684_, lean_object* v_i_3685_, lean_object* v_cs_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
uint8_t v_a_29061__boxed_3693_; lean_object* v_res_3694_; 
v_a_29061__boxed_3693_ = lean_unbox(v_a_3681_);
v_res_3694_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3677_, v_positions_3678_, v_recFnNames_3679_, v_containsRecFn_3680_, v_a_29061__boxed_3693_, v_e_3682_, v_as_3683_, v_bs_3684_, v_i_3685_, v_cs_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v_bs_3684_);
lean_dec_ref(v_as_3683_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3695_, lean_object* v_positions_3696_, lean_object* v_recFnNames_3697_, lean_object* v_containsRecFn_3698_, lean_object* v_below_3699_, lean_object* v_e_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_, lean_object* v_x_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3695_, v_positions_3696_, v_recFnNames_3697_, v_containsRecFn_3698_, v_below_3699_, v_e_3700_, v_x_3701_, v_x_3702_, v_x_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3711_, lean_object* v_positions_3712_, lean_object* v_recFnNames_3713_, lean_object* v_containsRecFn_3714_, lean_object* v_below_3715_, lean_object* v_e_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3711_, v_positions_3712_, v_recFnNames_3713_, v_containsRecFn_3714_, v_below_3715_, v_e_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
lean_dec(v_a_3721_);
lean_dec(v_a_3719_);
lean_dec_ref(v_a_3718_);
lean_dec(v_a_3717_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3724_, lean_object* v_msg_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3725_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3733_, lean_object* v_msg_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3733_, v_msg_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3742_, lean_object* v_name_3743_, lean_object* v_type_3744_, lean_object* v_val_3745_, lean_object* v_k_3746_, uint8_t v_nondep_3747_, uint8_t v_kind_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3743_, v_type_3744_, v_val_3745_, v_k_3746_, v_nondep_3747_, v_kind_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3756_, lean_object* v_name_3757_, lean_object* v_type_3758_, lean_object* v_val_3759_, lean_object* v_k_3760_, lean_object* v_nondep_3761_, lean_object* v_kind_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
uint8_t v_nondep_boxed_3769_; uint8_t v_kind_boxed_3770_; lean_object* v_res_3771_; 
v_nondep_boxed_3769_ = lean_unbox(v_nondep_3761_);
v_kind_boxed_3770_ = lean_unbox(v_kind_3762_);
v_res_3771_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3756_, v_name_3757_, v_type_3758_, v_val_3759_, v_k_3760_, v_nondep_boxed_3769_, v_kind_boxed_3770_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3772_, v___y_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3788_, lean_object* v_msg_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3788_, v_msg_3789_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3797_, lean_object* v_msg_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3797_, v_msg_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3806_, lean_object* v_constName_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3815_, lean_object* v_constName_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3815_, v_constName_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3824_, lean_object* v_ref_3825_, lean_object* v_constName_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3825_, v_constName_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3834_, lean_object* v_ref_3835_, lean_object* v_constName_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3834_, v_ref_3835_, v_constName_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v_ref_3835_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3844_, lean_object* v_ref_3845_, lean_object* v_msg_3846_, lean_object* v_declHint_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3845_, v_msg_3846_, v_declHint_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3855_, lean_object* v_ref_3856_, lean_object* v_msg_3857_, lean_object* v_declHint_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3855_, v_ref_3856_, v_msg_3857_, v_declHint_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec(v_ref_3856_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3866_, lean_object* v_declHint_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3866_, v_declHint_3867_, v___y_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3875_, lean_object* v_declHint_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3875_, v_declHint_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3884_, lean_object* v_ref_3885_, lean_object* v_msg_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3885_, v_msg_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3894_, lean_object* v_ref_3895_, lean_object* v_msg_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3894_, v_ref_3895_, v_msg_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec(v_ref_3895_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3904_, lean_object* v_e_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v_fst_3914_; lean_object* v_snd_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3912_ = lean_st_ref_take(v___y_3906_);
v___x_3913_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3904_, v_e_3905_, v___x_3912_);
v_fst_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_fst_3914_);
v_snd_3915_ = lean_ctor_get(v___x_3913_, 1);
lean_inc(v_snd_3915_);
lean_dec_ref(v___x_3913_);
v___x_3916_ = lean_st_ref_put(v___y_3906_, v_snd_3915_);
v___x_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3917_, 0, v_fst_3914_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3918_, lean_object* v_e_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3918_, v_e_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v_recFnNames_3918_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3927_, size_t v_i_3928_, lean_object* v_bs_3929_){
_start:
{
uint8_t v___x_3930_; 
v___x_3930_ = lean_usize_dec_lt(v_i_3928_, v_sz_3927_);
if (v___x_3930_ == 0)
{
return v_bs_3929_;
}
else
{
lean_object* v_v_3931_; lean_object* v_fnName_3932_; lean_object* v___x_3933_; lean_object* v_bs_x27_3934_; size_t v___x_3935_; size_t v___x_3936_; lean_object* v___x_3937_; 
v_v_3931_ = lean_array_uget_borrowed(v_bs_3929_, v_i_3928_);
v_fnName_3932_ = lean_ctor_get(v_v_3931_, 0);
lean_inc(v_fnName_3932_);
v___x_3933_ = lean_unsigned_to_nat(0u);
v_bs_x27_3934_ = lean_array_uset(v_bs_3929_, v_i_3928_, v___x_3933_);
v___x_3935_ = ((size_t)1ULL);
v___x_3936_ = lean_usize_add(v_i_3928_, v___x_3935_);
v___x_3937_ = lean_array_uset(v_bs_x27_3934_, v_i_3928_, v_fnName_3932_);
v_i_3928_ = v___x_3936_;
v_bs_3929_ = v___x_3937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3939_, lean_object* v_i_3940_, lean_object* v_bs_3941_){
_start:
{
size_t v_sz_boxed_3942_; size_t v_i_boxed_3943_; lean_object* v_res_3944_; 
v_sz_boxed_3942_ = lean_unbox_usize(v_sz_3939_);
lean_dec(v_sz_3939_);
v_i_boxed_3943_ = lean_unbox_usize(v_i_3940_);
lean_dec(v_i_3940_);
v_res_3944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3942_, v_i_boxed_3943_, v_bs_3941_);
return v_res_3944_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3945_ = lean_box(0);
v___x_3946_ = lean_unsigned_to_nat(16u);
v___x_3947_ = lean_mk_array(v___x_3946_, v___x_3945_);
return v___x_3947_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3948_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3949_ = lean_unsigned_to_nat(0u);
v___x_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
lean_ctor_set(v___x_3950_, 1, v___x_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3951_, lean_object* v_positions_3952_, lean_object* v_below_3953_, lean_object* v_e_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; size_t v_sz_3962_; size_t v___x_3963_; lean_object* v_recFnNames_3964_; lean_object* v_containsRecFn_3965_; lean_object* v___x_3966_; 
v___x_3960_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3961_ = lean_st_mk_ref(v___x_3960_);
v_sz_3962_ = lean_array_size(v_recArgInfos_3951_);
v___x_3963_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3951_);
v_recFnNames_3964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3962_, v___x_3963_, v_recArgInfos_3951_);
lean_inc_ref(v_recFnNames_3964_);
v_containsRecFn_3965_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_3965_, 0, v_recFnNames_3964_);
lean_inc_ref(v_a_3957_);
v___x_3966_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3951_, v_positions_3952_, v_recFnNames_3964_, v_containsRecFn_3965_, v_below_3953_, v_e_3954_, v___x_3961_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3975_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3969_ = v___x_3966_;
v_isShared_3970_ = v_isSharedCheck_3975_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3975_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3971_ = lean_st_ref_get(v___x_3961_);
lean_dec(v___x_3961_);
lean_dec(v___x_3971_);
if (v_isShared_3970_ == 0)
{
v___x_3973_ = v___x_3969_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3967_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
else
{
lean_dec(v___x_3961_);
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_3976_, lean_object* v_positions_3977_, lean_object* v_below_3978_, lean_object* v_e_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_3976_, v_positions_3977_, v_below_3978_, v_e_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_3986_, lean_object* v_k_3987_, uint8_t v_cleanupAnnotations_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v___f_3994_; uint8_t v___x_3995_; uint8_t v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___f_3994_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3994_, 0, v_k_3987_);
v___x_3995_ = 1;
v___x_3996_ = 0;
v___x_3997_ = lean_box(0);
v___x_3998_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3986_, v___x_3995_, v___x_3996_, v___x_3995_, v___x_3996_, v___x_3997_, v___f_3994_, v_cleanupAnnotations_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
v_a_4007_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3998_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3998_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4015_, lean_object* v_k_4016_, lean_object* v_cleanupAnnotations_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4023_; lean_object* v_res_4024_; 
v_cleanupAnnotations_boxed_4023_ = lean_unbox(v_cleanupAnnotations_4017_);
v_res_4024_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4015_, v_k_4016_, v_cleanupAnnotations_boxed_4023_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4025_, lean_object* v_e_4026_, lean_object* v_k_4027_, uint8_t v_cleanupAnnotations_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4026_, v_k_4027_, v_cleanupAnnotations_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4035_, lean_object* v_e_4036_, lean_object* v_k_4037_, lean_object* v_cleanupAnnotations_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4044_; lean_object* v_res_4045_; 
v_cleanupAnnotations_boxed_4044_ = lean_unbox(v_cleanupAnnotations_4038_);
v_res_4045_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4035_, v_e_4036_, v_k_4037_, v_cleanupAnnotations_boxed_4044_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4046_, lean_object* v_recArgInfo_4047_, lean_object* v_xs_4048_, lean_object* v___value_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_Meta_instantiateForall(v_type_4046_, v_xs_4048_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4057_; lean_object* v_fst_4058_; lean_object* v_snd_4059_; uint8_t v___x_4060_; uint8_t v___x_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v___x_4057_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4047_, v_xs_4048_);
v_fst_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_fst_4058_);
v_snd_4059_ = lean_ctor_get(v___x_4057_, 1);
lean_inc(v_snd_4059_);
lean_dec_ref(v___x_4057_);
v___x_4060_ = 0;
v___x_4061_ = 1;
v___x_4062_ = 1;
v___x_4063_ = l_Lean_Meta_mkForallFVars(v_snd_4059_, v_a_4056_, v___x_4060_, v___x_4061_, v___x_4061_, v___x_4062_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v_snd_4059_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4065_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = l_Lean_Meta_mkLambdaFVars(v_fst_4058_, v_a_4064_, v___x_4060_, v___x_4061_, v___x_4060_, v___x_4061_, v___x_4062_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v_fst_4058_);
return v___x_4065_;
}
else
{
lean_dec(v_fst_4058_);
return v___x_4063_;
}
}
else
{
lean_dec_ref(v_xs_4048_);
lean_dec_ref(v_recArgInfo_4047_);
return v___x_4055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4066_, lean_object* v_recArgInfo_4067_, lean_object* v_xs_4068_, lean_object* v___value_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4066_, v_recArgInfo_4067_, v_xs_4068_, v___value_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec_ref(v___value_4069_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4076_, lean_object* v_value_4077_, lean_object* v_type_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_){
_start:
{
lean_object* v___f_4084_; uint8_t v___x_4085_; lean_object* v___x_4086_; 
v___f_4084_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4084_, 0, v_type_4078_);
lean_closure_set(v___f_4084_, 1, v_recArgInfo_4076_);
v___x_4085_ = 0;
v___x_4086_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4077_, v___f_4084_, v___x_4085_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4087_, lean_object* v_value_4088_, lean_object* v_type_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4087_, v_value_4088_, v_type_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4096_, lean_object* v_maxFVars_x3f_4097_, lean_object* v_k_4098_, uint8_t v_cleanupAnnotations_4099_, uint8_t v_whnfType_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___f_4106_; lean_object* v___x_4107_; 
v___f_4106_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4106_, 0, v_k_4098_);
v___x_4107_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4096_, v_maxFVars_x3f_4097_, v___f_4106_, v_cleanupAnnotations_4099_, v_whnfType_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
v_a_4116_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4107_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4107_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4124_, lean_object* v_maxFVars_x3f_4125_, lean_object* v_k_4126_, lean_object* v_cleanupAnnotations_4127_, lean_object* v_whnfType_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4134_; uint8_t v_whnfType_boxed_4135_; lean_object* v_res_4136_; 
v_cleanupAnnotations_boxed_4134_ = lean_unbox(v_cleanupAnnotations_4127_);
v_whnfType_boxed_4135_ = lean_unbox(v_whnfType_4128_);
v_res_4136_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4124_, v_maxFVars_x3f_4125_, v_k_4126_, v_cleanupAnnotations_boxed_4134_, v_whnfType_boxed_4135_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4137_, lean_object* v_type_4138_, lean_object* v_maxFVars_x3f_4139_, lean_object* v_k_4140_, uint8_t v_cleanupAnnotations_4141_, uint8_t v_whnfType_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4138_, v_maxFVars_x3f_4139_, v_k_4140_, v_cleanupAnnotations_4141_, v_whnfType_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4149_, lean_object* v_type_4150_, lean_object* v_maxFVars_x3f_4151_, lean_object* v_k_4152_, lean_object* v_cleanupAnnotations_4153_, lean_object* v_whnfType_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4160_; uint8_t v_whnfType_boxed_4161_; lean_object* v_res_4162_; 
v_cleanupAnnotations_boxed_4160_ = lean_unbox(v_cleanupAnnotations_4153_);
v_whnfType_boxed_4161_ = lean_unbox(v_whnfType_4154_);
v_res_4162_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4149_, v_type_4150_, v_maxFVars_x3f_4151_, v_k_4152_, v_cleanupAnnotations_boxed_4160_, v_whnfType_boxed_4161_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4163_, lean_object* v_recArgInfos_4164_, lean_object* v_positions_4165_, lean_object* v_value_4166_, lean_object* v_fst_4167_, lean_object* v_snd_4168_, lean_object* v_below_4169_, lean_object* v_x_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4176_ = lean_unsigned_to_nat(0u);
v___x_4177_ = lean_array_get_borrowed(v___x_4163_, v_below_4169_, v___x_4176_);
lean_inc(v___x_4177_);
v___x_4178_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4164_, v_positions_4165_, v___x_4177_, v_value_4166_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; uint8_t v___x_4186_; uint8_t v___x_4187_; lean_object* v___x_4188_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___x_4178_, 1);
v___x_4180_ = lean_unsigned_to_nat(1u);
v___x_4181_ = lean_mk_empty_array_with_capacity(v___x_4180_);
lean_inc(v___x_4177_);
v___x_4182_ = lean_array_push(v___x_4181_, v___x_4177_);
v___x_4183_ = l_Array_append___redArg(v_fst_4167_, v___x_4182_);
lean_dec_ref(v___x_4182_);
v___x_4184_ = l_Array_append___redArg(v___x_4183_, v_snd_4168_);
v___x_4185_ = 0;
v___x_4186_ = 1;
v___x_4187_ = 1;
v___x_4188_ = l_Lean_Meta_mkLambdaFVars(v___x_4184_, v_a_4179_, v___x_4185_, v___x_4186_, v___x_4185_, v___x_4186_, v___x_4187_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec_ref(v___x_4184_);
return v___x_4188_;
}
else
{
lean_dec_ref(v_fst_4167_);
return v___x_4178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4189_, lean_object* v_recArgInfos_4190_, lean_object* v_positions_4191_, lean_object* v_value_4192_, lean_object* v_fst_4193_, lean_object* v_snd_4194_, lean_object* v_below_4195_, lean_object* v_x_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4189_, v_recArgInfos_4190_, v_positions_4191_, v_value_4192_, v_fst_4193_, v_snd_4194_, v_below_4195_, v_x_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_x_4196_);
lean_dec_ref(v_below_4195_);
lean_dec_ref(v_snd_4194_);
lean_dec_ref(v___x_4189_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4205_, lean_object* v_FType_4206_, lean_object* v___x_4207_, lean_object* v_recArgInfos_4208_, lean_object* v_positions_4209_, lean_object* v_xs_4210_, lean_object* v_value_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; lean_object* v_fst_4218_; lean_object* v_snd_4219_; lean_object* v___x_4220_; 
v___x_4217_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4205_, v_xs_4210_);
v_fst_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_fst_4218_);
v_snd_4219_ = lean_ctor_get(v___x_4217_, 1);
lean_inc(v_snd_4219_);
lean_dec_ref(v___x_4217_);
v___x_4220_ = l_Lean_Meta_instantiateForall(v_FType_4206_, v_fst_4218_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___f_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; lean_object* v___x_4225_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4222_, 0, v___x_4207_);
lean_closure_set(v___f_4222_, 1, v_recArgInfos_4208_);
lean_closure_set(v___f_4222_, 2, v_positions_4209_);
lean_closure_set(v___f_4222_, 3, v_value_4211_);
lean_closure_set(v___f_4222_, 4, v_fst_4218_);
lean_closure_set(v___f_4222_, 5, v_snd_4219_);
v___x_4223_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4224_ = 0;
v___x_4225_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4221_, v___x_4223_, v___f_4222_, v___x_4224_, v___x_4224_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
return v___x_4225_;
}
else
{
lean_dec(v_snd_4219_);
lean_dec(v_fst_4218_);
lean_dec_ref(v_value_4211_);
lean_dec_ref(v_positions_4209_);
lean_dec_ref(v_recArgInfos_4208_);
lean_dec_ref(v___x_4207_);
return v___x_4220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4226_, lean_object* v_FType_4227_, lean_object* v___x_4228_, lean_object* v_recArgInfos_4229_, lean_object* v_positions_4230_, lean_object* v_xs_4231_, lean_object* v_value_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4226_, v_FType_4227_, v___x_4228_, v_recArgInfos_4229_, v_positions_4230_, v_xs_4231_, v_value_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4239_, lean_object* v_positions_4240_, lean_object* v_recArgInfo_4241_, lean_object* v_value_4242_, lean_object* v_FType_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_){
_start:
{
lean_object* v___x_4249_; lean_object* v___f_4250_; uint8_t v___x_4251_; lean_object* v___x_4252_; 
v___x_4249_ = l_Lean_instInhabitedExpr;
v___f_4250_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4250_, 0, v_recArgInfo_4241_);
lean_closure_set(v___f_4250_, 1, v_FType_4243_);
lean_closure_set(v___f_4250_, 2, v___x_4249_);
lean_closure_set(v___f_4250_, 3, v_recArgInfos_4239_);
lean_closure_set(v___f_4250_, 4, v_positions_4240_);
v___x_4251_ = 0;
v___x_4252_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4242_, v___f_4250_, v___x_4251_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4253_, lean_object* v_positions_4254_, lean_object* v_recArgInfo_4255_, lean_object* v_value_4256_, lean_object* v_FType_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4253_, v_positions_4254_, v_recArgInfo_4255_, v_value_4256_, v_FType_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_);
lean_dec(v_a_4261_);
lean_dec_ref(v_a_4260_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4264_, lean_object* v_params_4265_, uint8_t v_isIndPred_4266_, lean_object* v_brecOnUniv_4267_, lean_object* v_levels_4268_, lean_object* v_idx_4269_){
_start:
{
lean_object* v_n_4270_; lean_object* v___y_4272_; 
v_n_4270_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4264_, v_idx_4269_);
if (v_isIndPred_4266_ == 0)
{
lean_object* v___x_4275_; 
v___x_4275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4275_, 0, v_brecOnUniv_4267_);
lean_ctor_set(v___x_4275_, 1, v_levels_4268_);
v___y_4272_ = v___x_4275_;
goto v___jp_4271_;
}
else
{
lean_dec(v_brecOnUniv_4267_);
v___y_4272_ = v_levels_4268_;
goto v___jp_4271_;
}
v___jp_4271_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = l_Lean_Expr_const___override(v_n_4270_, v___y_4272_);
v___x_4274_ = l_Lean_mkAppN(v___x_4273_, v_params_4265_);
return v___x_4274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4276_, lean_object* v_params_4277_, lean_object* v_isIndPred_4278_, lean_object* v_brecOnUniv_4279_, lean_object* v_levels_4280_, lean_object* v_idx_4281_){
_start:
{
uint8_t v_isIndPred_boxed_4282_; lean_object* v_res_4283_; 
v_isIndPred_boxed_4282_ = lean_unbox(v_isIndPred_4278_);
v_res_4283_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4276_, v_params_4277_, v_isIndPred_boxed_4282_, v_brecOnUniv_4279_, v_levels_4280_, v_idx_4281_);
lean_dec(v_idx_4281_);
lean_dec_ref(v_params_4277_);
lean_dec_ref(v_toIndGroupInfo_4276_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4284_, lean_object* v_a_4285_, lean_object* v_n_4286_){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = lean_apply_1(v_brecOnCons_4284_, v_n_4286_);
v___x_4288_ = l_Lean_mkAppN(v___x_4287_, v_a_4285_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4289_, lean_object* v_a_4290_, lean_object* v_n_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4289_, v_a_4290_, v_n_4291_);
lean_dec_ref(v_a_4290_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4293_, lean_object* v_type_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Lean_Meta_getLevel(v_type_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4301_, lean_object* v_type_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4301_, v_type_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v_x_4301_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4309_, size_t v_sz_4310_, size_t v_i_4311_, lean_object* v_bs_4312_){
_start:
{
uint8_t v___x_4313_; 
v___x_4313_ = lean_usize_dec_lt(v_i_4311_, v_sz_4310_);
if (v___x_4313_ == 0)
{
return v_bs_4312_;
}
else
{
lean_object* v___x_4314_; lean_object* v_v_4315_; lean_object* v___x_4316_; lean_object* v_bs_x27_4317_; lean_object* v___x_4318_; size_t v___x_4319_; size_t v___x_4320_; lean_object* v___x_4321_; 
v___x_4314_ = l_Lean_instInhabitedExpr;
v_v_4315_ = lean_array_uget(v_bs_4312_, v_i_4311_);
v___x_4316_ = lean_unsigned_to_nat(0u);
v_bs_x27_4317_ = lean_array_uset(v_bs_4312_, v_i_4311_, v___x_4316_);
v___x_4318_ = lean_array_get_borrowed(v___x_4314_, v_xs_4309_, v_v_4315_);
lean_dec(v_v_4315_);
v___x_4319_ = ((size_t)1ULL);
v___x_4320_ = lean_usize_add(v_i_4311_, v___x_4319_);
lean_inc(v___x_4318_);
v___x_4321_ = lean_array_uset(v_bs_x27_4317_, v_i_4311_, v___x_4318_);
v_i_4311_ = v___x_4320_;
v_bs_4312_ = v___x_4321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4323_, lean_object* v_sz_4324_, lean_object* v_i_4325_, lean_object* v_bs_4326_){
_start:
{
size_t v_sz_boxed_4327_; size_t v_i_boxed_4328_; lean_object* v_res_4329_; 
v_sz_boxed_4327_ = lean_unbox_usize(v_sz_4324_);
lean_dec(v_sz_4324_);
v_i_boxed_4328_ = lean_unbox_usize(v_i_4325_);
lean_dec(v_i_4325_);
v_res_4329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4323_, v_sz_boxed_4327_, v_i_boxed_4328_, v_bs_4326_);
lean_dec_ref(v_xs_4323_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4330_, lean_object* v_f_4331_, lean_object* v_as_4332_, lean_object* v_bs_4333_, lean_object* v_i_4334_, lean_object* v_cs_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v___x_4341_; uint8_t v___x_4342_; 
v___x_4341_ = lean_array_get_size(v_as_4332_);
v___x_4342_ = lean_nat_dec_lt(v_i_4334_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_object* v___x_4343_; 
lean_dec(v_i_4334_);
lean_dec_ref(v_f_4331_);
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v_cs_4335_);
return v___x_4343_;
}
else
{
lean_object* v___x_4344_; uint8_t v___x_4345_; 
v___x_4344_ = lean_array_get_size(v_bs_4333_);
v___x_4345_ = lean_nat_dec_lt(v_i_4334_, v___x_4344_);
if (v___x_4345_ == 0)
{
lean_object* v___x_4346_; 
lean_dec(v_i_4334_);
lean_dec_ref(v_f_4331_);
v___x_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4346_, 0, v_cs_4335_);
return v___x_4346_;
}
else
{
lean_object* v_a_4347_; lean_object* v_b_4348_; size_t v_sz_4349_; size_t v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v_a_4347_ = lean_array_fget_borrowed(v_as_4332_, v_i_4334_);
v_b_4348_ = lean_array_fget_borrowed(v_bs_4333_, v_i_4334_);
v_sz_4349_ = lean_array_size(v_b_4348_);
v___x_4350_ = ((size_t)0ULL);
lean_inc(v_b_4348_);
v___x_4351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4330_, v_sz_4349_, v___x_4350_, v_b_4348_);
lean_inc_ref(v_f_4331_);
lean_inc(v___y_4339_);
lean_inc_ref(v___y_4338_);
lean_inc(v___y_4337_);
lean_inc_ref(v___y_4336_);
lean_inc(v_a_4347_);
v___x_4352_ = lean_apply_7(v_f_4331_, v_a_4347_, v___x_4351_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, lean_box(0));
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v___x_4354_ = lean_unsigned_to_nat(1u);
v___x_4355_ = lean_nat_add(v_i_4334_, v___x_4354_);
lean_dec(v_i_4334_);
v___x_4356_ = lean_array_push(v_cs_4335_, v_a_4353_);
v_i_4334_ = v___x_4355_;
v_cs_4335_ = v___x_4356_;
goto _start;
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec_ref(v_cs_4335_);
lean_dec(v_i_4334_);
lean_dec_ref(v_f_4331_);
v_a_4358_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4352_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4352_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4366_, lean_object* v_f_4367_, lean_object* v_as_4368_, lean_object* v_bs_4369_, lean_object* v_i_4370_, lean_object* v_cs_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4366_, v_f_4367_, v_as_4368_, v_bs_4369_, v_i_4370_, v_cs_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec_ref(v_bs_4369_);
lean_dec_ref(v_as_4368_);
lean_dec_ref(v_xs_4366_);
return v_res_4377_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l_Array_instInhabited(lean_box(0));
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v___x_4385_; lean_object* v_toApplicative_4386_; lean_object* v_toFunctor_4387_; lean_object* v_toSeq_4388_; lean_object* v_toSeqLeft_4389_; lean_object* v_toSeqRight_4390_; lean_object* v___f_4391_; lean_object* v___f_4392_; lean_object* v___f_4393_; lean_object* v___f_4394_; lean_object* v___x_4395_; lean_object* v___f_4396_; lean_object* v___f_4397_; lean_object* v___f_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v_toApplicative_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4433_; 
v___x_4385_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4386_ = lean_ctor_get(v___x_4385_, 0);
v_toFunctor_4387_ = lean_ctor_get(v_toApplicative_4386_, 0);
v_toSeq_4388_ = lean_ctor_get(v_toApplicative_4386_, 2);
v_toSeqLeft_4389_ = lean_ctor_get(v_toApplicative_4386_, 3);
v_toSeqRight_4390_ = lean_ctor_get(v_toApplicative_4386_, 4);
v___f_4391_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4392_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4387_, 2);
v___f_4393_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4393_, 0, v_toFunctor_4387_);
v___f_4394_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4394_, 0, v_toFunctor_4387_);
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___f_4393_);
lean_ctor_set(v___x_4395_, 1, v___f_4394_);
lean_inc(v_toSeqRight_4390_);
v___f_4396_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4396_, 0, v_toSeqRight_4390_);
lean_inc(v_toSeqLeft_4389_);
v___f_4397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4397_, 0, v_toSeqLeft_4389_);
lean_inc(v_toSeq_4388_);
v___f_4398_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4398_, 0, v_toSeq_4388_);
v___x_4399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4395_);
lean_ctor_set(v___x_4399_, 1, v___f_4391_);
lean_ctor_set(v___x_4399_, 2, v___f_4398_);
lean_ctor_set(v___x_4399_, 3, v___f_4397_);
lean_ctor_set(v___x_4399_, 4, v___f_4396_);
v___x_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
lean_ctor_set(v___x_4400_, 1, v___f_4392_);
v___x_4401_ = l_StateRefT_x27_instMonad___redArg(v___x_4400_);
v_toApplicative_4402_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4433_ == 0)
{
lean_object* v_unused_4434_; 
v_unused_4434_ = lean_ctor_get(v___x_4401_, 1);
lean_dec(v_unused_4434_);
v___x_4404_ = v___x_4401_;
v_isShared_4405_ = v_isSharedCheck_4433_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_toApplicative_4402_);
lean_dec(v___x_4401_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4433_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v_toFunctor_4406_; lean_object* v_toSeq_4407_; lean_object* v_toSeqLeft_4408_; lean_object* v_toSeqRight_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4431_; 
v_toFunctor_4406_ = lean_ctor_get(v_toApplicative_4402_, 0);
v_toSeq_4407_ = lean_ctor_get(v_toApplicative_4402_, 2);
v_toSeqLeft_4408_ = lean_ctor_get(v_toApplicative_4402_, 3);
v_toSeqRight_4409_ = lean_ctor_get(v_toApplicative_4402_, 4);
v_isSharedCheck_4431_ = !lean_is_exclusive(v_toApplicative_4402_);
if (v_isSharedCheck_4431_ == 0)
{
lean_object* v_unused_4432_; 
v_unused_4432_ = lean_ctor_get(v_toApplicative_4402_, 1);
lean_dec(v_unused_4432_);
v___x_4411_ = v_toApplicative_4402_;
v_isShared_4412_ = v_isSharedCheck_4431_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_toSeqRight_4409_);
lean_inc(v_toSeqLeft_4408_);
lean_inc(v_toSeq_4407_);
lean_inc(v_toFunctor_4406_);
lean_dec(v_toApplicative_4402_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4431_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___f_4413_; lean_object* v___f_4414_; lean_object* v___f_4415_; lean_object* v___f_4416_; lean_object* v___x_4417_; lean_object* v___f_4418_; lean_object* v___f_4419_; lean_object* v___f_4420_; lean_object* v___x_4422_; 
v___f_4413_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4414_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4406_);
v___f_4415_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4415_, 0, v_toFunctor_4406_);
v___f_4416_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4416_, 0, v_toFunctor_4406_);
v___x_4417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___f_4415_);
lean_ctor_set(v___x_4417_, 1, v___f_4416_);
v___f_4418_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4418_, 0, v_toSeqRight_4409_);
v___f_4419_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4419_, 0, v_toSeqLeft_4408_);
v___f_4420_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4420_, 0, v_toSeq_4407_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 4, v___f_4418_);
lean_ctor_set(v___x_4411_, 3, v___f_4419_);
lean_ctor_set(v___x_4411_, 2, v___f_4420_);
lean_ctor_set(v___x_4411_, 1, v___f_4413_);
lean_ctor_set(v___x_4411_, 0, v___x_4417_);
v___x_4422_ = v___x_4411_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4417_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v___f_4413_);
lean_ctor_set(v_reuseFailAlloc_4430_, 2, v___f_4420_);
lean_ctor_set(v_reuseFailAlloc_4430_, 3, v___f_4419_);
lean_ctor_set(v_reuseFailAlloc_4430_, 4, v___f_4418_);
v___x_4422_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4424_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 1, v___f_4414_);
lean_ctor_set(v___x_4404_, 0, v___x_4422_);
v___x_4424_ = v___x_4404_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v___f_4414_);
v___x_4424_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_855__overap_4427_; lean_object* v___x_4428_; 
v___x_4425_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4426_ = l_instInhabitedOfMonad___redArg(v___x_4424_, v___x_4425_);
v___x_855__overap_4427_ = lean_panic_fn_borrowed(v___x_4426_, v_msg_4379_);
lean_dec(v___x_4426_);
lean_inc(v___y_4383_);
lean_inc_ref(v___y_4382_);
lean_inc(v___y_4381_);
lean_inc_ref(v___y_4380_);
v___x_4428_ = lean_apply_5(v___x_855__overap_4427_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, lean_box(0));
return v___x_4428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
return v_res_4441_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4445_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4446_ = lean_unsigned_to_nat(2u);
v___x_4447_ = lean_unsigned_to_nat(73u);
v___x_4448_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4449_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4450_ = l_mkPanicMessageWithDecl(v___x_4449_, v___x_4448_, v___x_4447_, v___x_4446_, v___x_4445_);
return v___x_4450_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4452_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4453_ = lean_unsigned_to_nat(2u);
v___x_4454_ = lean_unsigned_to_nat(74u);
v___x_4455_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4456_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4457_ = l_mkPanicMessageWithDecl(v___x_4456_, v___x_4455_, v___x_4454_, v___x_4453_, v___x_4452_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4460_, lean_object* v_positions_4461_, lean_object* v_ys_4462_, lean_object* v_xs_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; uint8_t v___x_4471_; 
v___x_4469_ = lean_array_get_size(v_positions_4461_);
v___x_4470_ = lean_array_get_size(v_ys_4462_);
v___x_4471_ = lean_nat_dec_eq(v___x_4469_, v___x_4470_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
lean_dec_ref(v_f_4460_);
v___x_4472_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4473_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4472_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4473_;
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; uint8_t v___x_4476_; 
v___x_4474_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4461_);
v___x_4475_ = lean_array_get_size(v_xs_4463_);
v___x_4476_ = lean_nat_dec_eq(v___x_4474_, v___x_4475_);
lean_dec(v___x_4474_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
lean_dec_ref(v_f_4460_);
v___x_4477_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4478_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4477_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4478_;
}
else
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4479_ = lean_unsigned_to_nat(0u);
v___x_4480_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4481_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4463_, v_f_4460_, v_ys_4462_, v_positions_4461_, v___x_4479_, v___x_4480_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4482_, lean_object* v_positions_4483_, lean_object* v_ys_4484_, lean_object* v_xs_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4482_, v_positions_4483_, v_ys_4484_, v_xs_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v_xs_4485_);
lean_dec_ref(v_ys_4484_);
lean_dec_ref(v_positions_4483_);
return v_res_4491_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = lean_unsigned_to_nat(0u);
v___x_4494_ = l_Lean_Level_ofNat(v___x_4493_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4495_, lean_object* v_positions_4496_, lean_object* v_motives_4497_, uint8_t v_isIndPred_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v_indGroupInst_4507_; lean_object* v_brecOnUniv_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; 
v___x_4504_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4505_ = lean_unsigned_to_nat(0u);
v___x_4506_ = lean_array_get_borrowed(v___x_4504_, v_recArgInfos_4495_, v___x_4505_);
v_indGroupInst_4507_ = lean_ctor_get(v___x_4506_, 4);
if (v_isIndPred_4498_ == 0)
{
lean_object* v___f_4550_; lean_object* v___x_4551_; lean_object* v_motive_4552_; lean_object* v___x_4553_; 
v___f_4550_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4551_ = l_Lean_instInhabitedExpr;
v_motive_4552_ = lean_array_get_borrowed(v___x_4551_, v_motives_4497_, v___x_4505_);
lean_inc(v_motive_4552_);
v___x_4553_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4552_, v___f_4550_, v_isIndPred_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v___x_4553_, 1);
v_brecOnUniv_4509_ = v_a_4554_;
v___y_4510_ = v_a_4499_;
v___y_4511_ = v_a_4500_;
v___y_4512_ = v_a_4501_;
v___y_4513_ = v_a_4502_;
goto v___jp_4508_;
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
v_a_4555_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4553_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4553_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
else
{
lean_object* v___x_4563_; 
v___x_4563_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4509_ = v___x_4563_;
v___y_4510_ = v_a_4499_;
v___y_4511_ = v_a_4500_;
v___y_4512_ = v_a_4501_;
v___y_4513_ = v_a_4502_;
goto v___jp_4508_;
}
v___jp_4508_:
{
lean_object* v_toIndGroupInfo_4514_; lean_object* v_levels_4515_; lean_object* v_params_4516_; lean_object* v___x_4517_; lean_object* v_brecOnCons_4518_; lean_object* v_brecOnAux_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v_toIndGroupInfo_4514_ = lean_ctor_get(v_indGroupInst_4507_, 0);
v_levels_4515_ = lean_ctor_get(v_indGroupInst_4507_, 1);
v_params_4516_ = lean_ctor_get(v_indGroupInst_4507_, 2);
v___x_4517_ = lean_box(v_isIndPred_4498_);
lean_inc_n(v_levels_4515_, 2);
lean_inc(v_brecOnUniv_4509_);
lean_inc_ref(v_params_4516_);
lean_inc_ref(v_toIndGroupInfo_4514_);
v_brecOnCons_4518_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4518_, 0, v_toIndGroupInfo_4514_);
lean_closure_set(v_brecOnCons_4518_, 1, v_params_4516_);
lean_closure_set(v_brecOnCons_4518_, 2, v___x_4517_);
lean_closure_set(v_brecOnCons_4518_, 3, v_brecOnUniv_4509_);
lean_closure_set(v_brecOnCons_4518_, 4, v_levels_4515_);
v_brecOnAux_4519_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4514_, v_params_4516_, v_isIndPred_4498_, v_brecOnUniv_4509_, v_levels_4515_, v___x_4505_);
v___x_4520_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4514_);
v___x_4521_ = l_Lean_Meta_inferArgumentTypesN(v___x_4520_, v_brecOnAux_4519_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref_known(v___x_4521_, 1);
v___x_4523_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4524_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4523_, v_positions_4496_, v_a_4522_, v_motives_4497_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v_a_4522_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4533_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4527_ = v___x_4524_;
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4524_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___f_4529_; lean_object* v___x_4531_; 
v___f_4529_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4529_, 0, v_brecOnCons_4518_);
lean_closure_set(v___f_4529_, 1, v_a_4525_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v___f_4529_);
v___x_4531_ = v___x_4527_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___f_4529_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v_brecOnCons_4518_);
v_a_4534_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4524_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4524_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
lean_dec_ref(v_brecOnCons_4518_);
v_a_4542_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4521_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4521_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4564_, lean_object* v_positions_4565_, lean_object* v_motives_4566_, lean_object* v_isIndPred_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_){
_start:
{
uint8_t v_isIndPred_boxed_4573_; lean_object* v_res_4574_; 
v_isIndPred_boxed_4573_ = lean_unbox(v_isIndPred_4567_);
v_res_4574_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4564_, v_positions_4565_, v_motives_4566_, v_isIndPred_boxed_4573_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
lean_dec(v_a_4571_);
lean_dec_ref(v_a_4570_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec_ref(v_motives_4566_);
lean_dec_ref(v_positions_4565_);
lean_dec_ref(v_recArgInfos_4564_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4575_, lean_object* v_msg_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___x_4582_; 
v___x_4582_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4583_, lean_object* v_msg_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4583_, v_msg_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4591_, lean_object* v_00_u03b1_4592_, lean_object* v_f_4593_, lean_object* v_positions_4594_, lean_object* v_ys_4595_, lean_object* v_xs_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4593_, v_positions_4594_, v_ys_4595_, v_xs_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4603_, lean_object* v_00_u03b1_4604_, lean_object* v_f_4605_, lean_object* v_positions_4606_, lean_object* v_ys_4607_, lean_object* v_xs_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4603_, v_00_u03b1_4604_, v_f_4605_, v_positions_4606_, v_ys_4607_, v_xs_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec_ref(v_xs_4608_);
lean_dec_ref(v_ys_4607_);
lean_dec_ref(v_positions_4606_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4615_, lean_object* v_00_u03b3_4616_, lean_object* v_xs_4617_, lean_object* v_f_4618_, lean_object* v_as_4619_, lean_object* v_bs_4620_, lean_object* v_i_4621_, lean_object* v_cs_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4617_, v_f_4618_, v_as_4619_, v_bs_4620_, v_i_4621_, v_cs_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4629_, lean_object* v_00_u03b3_4630_, lean_object* v_xs_4631_, lean_object* v_f_4632_, lean_object* v_as_4633_, lean_object* v_bs_4634_, lean_object* v_i_4635_, lean_object* v_cs_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4629_, v_00_u03b3_4630_, v_xs_4631_, v_f_4632_, v_as_4633_, v_bs_4634_, v_i_4635_, v_cs_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec_ref(v_bs_4634_);
lean_dec_ref(v_as_4633_);
lean_dec_ref(v_xs_4631_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_4643_, lean_object* v_e_4644_){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = l_Lean_indentD(v_e_4644_);
v___x_4646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4643_);
lean_ctor_set(v___x_4646_, 1, v___x_4645_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_4647_, lean_object* v_x_4648_, lean_object* v_brecOnType_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4647_, v_brecOnType_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_4656_, lean_object* v_x_4657_, lean_object* v_brecOnType_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_4656_, v_x_4657_, v_brecOnType_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec_ref(v_x_4657_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4665_, lean_object* v_as_4666_, size_t v_sz_4667_, size_t v_i_4668_, lean_object* v_b_4669_){
_start:
{
uint8_t v___x_4671_; 
v___x_4671_ = lean_usize_dec_lt(v_i_4668_, v_sz_4667_);
if (v___x_4671_ == 0)
{
lean_object* v___x_4672_; 
lean_dec_ref(v_a_4665_);
v___x_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4672_, 0, v_b_4669_);
return v___x_4672_;
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4674_; size_t v___x_4675_; size_t v___x_4676_; 
v_a_4673_ = lean_array_uget_borrowed(v_as_4666_, v_i_4668_);
lean_inc_ref(v_a_4665_);
v___x_4674_ = lean_array_set(v_b_4669_, v_a_4673_, v_a_4665_);
v___x_4675_ = ((size_t)1ULL);
v___x_4676_ = lean_usize_add(v_i_4668_, v___x_4675_);
v_i_4668_ = v___x_4676_;
v_b_4669_ = v___x_4674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4678_, lean_object* v_as_4679_, lean_object* v_sz_4680_, lean_object* v_i_4681_, lean_object* v_b_4682_, lean_object* v___y_4683_){
_start:
{
size_t v_sz_boxed_4684_; size_t v_i_boxed_4685_; lean_object* v_res_4686_; 
v_sz_boxed_4684_ = lean_unbox_usize(v_sz_4680_);
lean_dec(v_sz_4680_);
v_i_boxed_4685_ = lean_unbox_usize(v_i_4681_);
lean_dec(v_i_4681_);
v_res_4686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4678_, v_as_4679_, v_sz_boxed_4684_, v_i_boxed_4685_, v_b_4682_);
lean_dec_ref(v_as_4679_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4687_, size_t v_sz_4688_, size_t v_i_4689_, lean_object* v_b_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
uint8_t v___x_4696_; 
v___x_4696_ = lean_usize_dec_lt(v_i_4689_, v_sz_4688_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; 
v___x_4697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4697_, 0, v_b_4690_);
return v___x_4697_;
}
else
{
lean_object* v_snd_4698_; lean_object* v_fst_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4743_; 
v_snd_4698_ = lean_ctor_get(v_b_4690_, 1);
v_fst_4699_ = lean_ctor_get(v_b_4690_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_b_4690_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4701_ = v_b_4690_;
v_isShared_4702_ = v_isSharedCheck_4743_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_snd_4698_);
lean_inc(v_fst_4699_);
lean_dec(v_b_4690_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4743_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v_array_4703_; lean_object* v_start_4704_; lean_object* v_stop_4705_; uint8_t v___x_4706_; 
v_array_4703_ = lean_ctor_get(v_snd_4698_, 0);
v_start_4704_ = lean_ctor_get(v_snd_4698_, 1);
v_stop_4705_ = lean_ctor_get(v_snd_4698_, 2);
v___x_4706_ = lean_nat_dec_lt(v_start_4704_, v_stop_4705_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4708_; 
if (v_isShared_4702_ == 0)
{
v___x_4708_ = v___x_4701_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_fst_4699_);
lean_ctor_set(v_reuseFailAlloc_4710_, 1, v_snd_4698_);
v___x_4708_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; 
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
return v___x_4709_;
}
}
else
{
lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4739_; 
lean_inc(v_stop_4705_);
lean_inc(v_start_4704_);
lean_inc_ref(v_array_4703_);
v_isSharedCheck_4739_ = !lean_is_exclusive(v_snd_4698_);
if (v_isSharedCheck_4739_ == 0)
{
lean_object* v_unused_4740_; lean_object* v_unused_4741_; lean_object* v_unused_4742_; 
v_unused_4740_ = lean_ctor_get(v_snd_4698_, 2);
lean_dec(v_unused_4740_);
v_unused_4741_ = lean_ctor_get(v_snd_4698_, 1);
lean_dec(v_unused_4741_);
v_unused_4742_ = lean_ctor_get(v_snd_4698_, 0);
lean_dec(v_unused_4742_);
v___x_4712_ = v_snd_4698_;
v_isShared_4713_ = v_isSharedCheck_4739_;
goto v_resetjp_4711_;
}
else
{
lean_dec(v_snd_4698_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4739_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v_a_4714_; lean_object* v___x_4715_; size_t v_sz_4716_; size_t v___x_4717_; lean_object* v___x_4718_; 
v_a_4714_ = lean_array_uget_borrowed(v_as_4687_, v_i_4689_);
v___x_4715_ = lean_array_fget_borrowed(v_array_4703_, v_start_4704_);
v_sz_4716_ = lean_array_size(v___x_4715_);
v___x_4717_ = ((size_t)0ULL);
lean_inc(v_a_4714_);
v___x_4718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4714_, v___x_4715_, v_sz_4716_, v___x_4717_, v_fst_4699_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4723_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4719_);
lean_dec_ref_known(v___x_4718_, 1);
v___x_4720_ = lean_unsigned_to_nat(1u);
v___x_4721_ = lean_nat_add(v_start_4704_, v___x_4720_);
lean_dec(v_start_4704_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 1, v___x_4721_);
v___x_4723_ = v___x_4712_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_array_4703_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v___x_4721_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_stop_4705_);
v___x_4723_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4725_; 
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 1, v___x_4723_);
lean_ctor_set(v___x_4701_, 0, v_a_4719_);
v___x_4725_ = v___x_4701_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_a_4719_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v___x_4723_);
v___x_4725_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
size_t v___x_4726_; size_t v___x_4727_; 
v___x_4726_ = ((size_t)1ULL);
v___x_4727_ = lean_usize_add(v_i_4689_, v___x_4726_);
v_i_4689_ = v___x_4727_;
v_b_4690_ = v___x_4725_;
goto _start;
}
}
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
lean_del_object(v___x_4712_);
lean_dec(v_stop_4705_);
lean_dec(v_start_4704_);
lean_dec_ref(v_array_4703_);
lean_del_object(v___x_4701_);
v_a_4731_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4718_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4718_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4744_, lean_object* v_sz_4745_, lean_object* v_i_4746_, lean_object* v_b_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
size_t v_sz_boxed_4753_; size_t v_i_boxed_4754_; lean_object* v_res_4755_; 
v_sz_boxed_4753_ = lean_unbox_usize(v_sz_4745_);
lean_dec(v_sz_4745_);
v_i_boxed_4754_ = lean_unbox_usize(v_i_4746_);
lean_dec(v_i_4746_);
v_res_4755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4744_, v_sz_boxed_4753_, v_i_boxed_4754_, v_b_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___y_4751_);
lean_dec_ref(v___y_4750_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
lean_dec_ref(v_as_4744_);
return v_res_4755_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4757_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4758_ = l_Lean_stringToMessageData(v___x_4757_);
return v___x_4758_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4759_; lean_object* v___f_4760_; 
v___x_4759_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4760_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_4760_, 0, v___x_4759_);
return v___f_4760_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4762_ = l_Lean_Expr_sort___override(v___x_4761_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4763_, lean_object* v_positions_4764_, lean_object* v_brecOnConst_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v_recArgInfo_4773_; lean_object* v_indicesPos_4774_; lean_object* v_indIdx_4775_; lean_object* v_brecOn_4776_; lean_object* v___f_4777_; uint8_t v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4771_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4772_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4773_ = lean_array_get_borrowed(v___x_4771_, v_recArgInfos_4763_, v___x_4772_);
v_indicesPos_4774_ = lean_ctor_get(v_recArgInfo_4773_, 3);
v_indIdx_4775_ = lean_ctor_get(v_recArgInfo_4773_, 5);
lean_inc(v_indIdx_4775_);
v_brecOn_4776_ = lean_apply_1(v_brecOnConst_4765_, v_indIdx_4775_);
v___f_4777_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4778_ = 0;
v___x_4779_ = lean_box(v___x_4778_);
lean_inc_ref(v_brecOn_4776_);
v___x_4780_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4780_, 0, v_brecOn_4776_);
lean_closure_set(v___x_4780_, 1, v___x_4779_);
v___x_4781_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4780_, v___f_4777_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v___x_4782_; 
lean_dec_ref_known(v___x_4781_, 1);
lean_inc(v_a_4769_);
lean_inc_ref(v_a_4768_);
lean_inc(v_a_4767_);
lean_inc_ref(v_a_4766_);
v___x_4782_ = lean_infer_type(v_brecOn_4776_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v_a_4783_; lean_object* v_numTypeFormers_4784_; lean_object* v___f_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; lean_object* v___x_4791_; 
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
lean_inc(v_a_4783_);
lean_dec_ref_known(v___x_4782_, 1);
v_numTypeFormers_4784_ = lean_array_get_size(v_positions_4764_);
v___f_4785_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4785_, 0, v_numTypeFormers_4784_);
v___x_4786_ = lean_array_get_size(v_indicesPos_4774_);
v___x_4787_ = lean_unsigned_to_nat(1u);
v___x_4788_ = lean_nat_add(v___x_4786_, v___x_4787_);
v___x_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
v___x_4790_ = 0;
v___x_4791_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4783_, v___x_4789_, v___f_4785_, v___x_4790_, v___x_4790_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_object* v_a_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; size_t v_sz_4798_; size_t v___x_4799_; lean_object* v___x_4800_; 
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
lean_inc(v_a_4792_);
lean_dec_ref_known(v___x_4791_, 1);
v___x_4793_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4764_);
v___x_4794_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4795_ = lean_mk_array(v___x_4793_, v___x_4794_);
v___x_4796_ = l_Array_toSubarray___redArg(v_positions_4764_, v___x_4772_, v_numTypeFormers_4784_);
v___x_4797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4795_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v_sz_4798_ = lean_array_size(v_a_4792_);
v___x_4799_ = ((size_t)0ULL);
v___x_4800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4792_, v_sz_4798_, v___x_4799_, v___x_4797_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
lean_dec(v_a_4792_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4809_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4803_ = v___x_4800_;
v_isShared_4804_ = v_isSharedCheck_4809_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4800_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4809_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v_fst_4805_; lean_object* v___x_4807_; 
v_fst_4805_ = lean_ctor_get(v_a_4801_, 0);
lean_inc(v_fst_4805_);
lean_dec(v_a_4801_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 0, v_fst_4805_);
v___x_4807_ = v___x_4803_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_fst_4805_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
v_a_4810_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4800_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4800_);
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
else
{
lean_dec_ref(v_positions_4764_);
return v___x_4791_;
}
}
else
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
lean_dec_ref(v_positions_4764_);
v_a_4818_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4782_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4782_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
lean_dec_ref(v_brecOn_4776_);
lean_dec_ref(v_positions_4764_);
v_a_4826_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4781_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4781_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4834_, lean_object* v_positions_4835_, lean_object* v_brecOnConst_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4834_, v_positions_4835_, v_brecOnConst_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec_ref(v_recArgInfos_4834_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4843_, lean_object* v_as_4844_, size_t v_sz_4845_, size_t v_i_4846_, lean_object* v_b_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4843_, v_as_4844_, v_sz_4845_, v_i_4846_, v_b_4847_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4854_, lean_object* v_as_4855_, lean_object* v_sz_4856_, lean_object* v_i_4857_, lean_object* v_b_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
size_t v_sz_boxed_4864_; size_t v_i_boxed_4865_; lean_object* v_res_4866_; 
v_sz_boxed_4864_ = lean_unbox_usize(v_sz_4856_);
lean_dec(v_sz_4856_);
v_i_boxed_4865_ = lean_unbox_usize(v_i_4857_);
lean_dec(v_i_4857_);
v_res_4866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4854_, v_as_4855_, v_sz_boxed_4864_, v_i_boxed_4865_, v_b_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
lean_dec_ref(v_as_4855_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4867_, lean_object* v_a_4868_){
_start:
{
if (lean_obj_tag(v_a_4867_) == 0)
{
lean_object* v___x_4869_; 
v___x_4869_ = l_List_reverse___redArg(v_a_4868_);
return v___x_4869_;
}
else
{
lean_object* v_head_4870_; lean_object* v_tail_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4882_; 
v_head_4870_ = lean_ctor_get(v_a_4867_, 0);
v_tail_4871_ = lean_ctor_get(v_a_4867_, 1);
v_isSharedCheck_4882_ = !lean_is_exclusive(v_a_4867_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4873_ = v_a_4867_;
v_isShared_4874_ = v_isSharedCheck_4882_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_tail_4871_);
lean_inc(v_head_4870_);
lean_dec(v_a_4867_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4882_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4875_ = l_Nat_reprFast(v_head_4870_);
v___x_4876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
v___x_4877_ = l_Lean_MessageData_ofFormat(v___x_4876_);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 1, v_a_4868_);
lean_ctor_set(v___x_4873_, 0, v___x_4877_);
v___x_4879_ = v___x_4873_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4877_);
lean_ctor_set(v_reuseFailAlloc_4881_, 1, v_a_4868_);
v___x_4879_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
v_a_4867_ = v_tail_4871_;
v_a_4868_ = v___x_4879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
if (lean_obj_tag(v_a_4883_) == 0)
{
lean_object* v___x_4885_; 
v___x_4885_ = l_List_reverse___redArg(v_a_4884_);
return v___x_4885_;
}
else
{
lean_object* v_head_4886_; lean_object* v_tail_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4899_; 
v_head_4886_ = lean_ctor_get(v_a_4883_, 0);
v_tail_4887_ = lean_ctor_get(v_a_4883_, 1);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_a_4883_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4889_ = v_a_4883_;
v_isShared_4890_ = v_isSharedCheck_4899_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_tail_4887_);
lean_inc(v_head_4886_);
lean_dec(v_a_4883_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4899_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4896_; 
v___x_4891_ = lean_array_to_list(v_head_4886_);
v___x_4892_ = lean_box(0);
v___x_4893_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4891_, v___x_4892_);
v___x_4894_ = l_Lean_MessageData_ofList(v___x_4893_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 1, v_a_4884_);
lean_ctor_set(v___x_4889_, 0, v___x_4894_);
v___x_4896_ = v___x_4889_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4894_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v_a_4884_);
v___x_4896_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
v_a_4883_ = v_tail_4887_;
v_a_4884_ = v___x_4896_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4900_, lean_object* v_v_4901_, lean_object* v_i_4902_){
_start:
{
lean_object* v___x_4903_; uint8_t v___x_4904_; 
v___x_4903_ = lean_array_get_size(v_xs_4900_);
v___x_4904_ = lean_nat_dec_lt(v_i_4902_, v___x_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; 
lean_dec(v_i_4902_);
v___x_4905_ = lean_box(0);
return v___x_4905_;
}
else
{
lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4906_ = lean_array_fget_borrowed(v_xs_4900_, v_i_4902_);
v___x_4907_ = lean_nat_dec_eq(v___x_4906_, v_v_4901_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = lean_unsigned_to_nat(1u);
v___x_4909_ = lean_nat_add(v_i_4902_, v___x_4908_);
lean_dec(v_i_4902_);
v_i_4902_ = v___x_4909_;
goto _start;
}
else
{
lean_object* v___x_4911_; 
v___x_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4911_, 0, v_i_4902_);
return v___x_4911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4912_, lean_object* v_v_4913_, lean_object* v_i_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4912_, v_v_4913_, v_i_4914_);
lean_dec(v_v_4913_);
lean_dec_ref(v_xs_4912_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4916_, lean_object* v_v_4917_){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = lean_unsigned_to_nat(0u);
v___x_4919_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4916_, v_v_4917_, v___x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4920_, lean_object* v_v_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4920_, v_v_4921_);
lean_dec(v_v_4921_);
lean_dec_ref(v_xs_4920_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4926_, lean_object* v_as_4927_, size_t v_sz_4928_, size_t v_i_4929_, lean_object* v_b_4930_){
_start:
{
uint8_t v___x_4931_; 
v___x_4931_ = lean_usize_dec_lt(v_i_4929_, v_sz_4928_);
if (v___x_4931_ == 0)
{
lean_inc_ref(v_b_4930_);
return v_b_4930_;
}
else
{
lean_object* v___x_4932_; lean_object* v_a_4933_; lean_object* v___x_4934_; 
v___x_4932_ = lean_box(0);
v_a_4933_ = lean_array_uget_borrowed(v_as_4927_, v_i_4929_);
v___x_4934_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4933_, v_fnIdx_4926_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v___x_4935_; size_t v___x_4936_; size_t v___x_4937_; 
v___x_4935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4936_ = ((size_t)1ULL);
v___x_4937_ = lean_usize_add(v_i_4929_, v___x_4936_);
v_i_4929_ = v___x_4937_;
v_b_4930_ = v___x_4935_;
goto _start;
}
else
{
lean_object* v_val_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4950_; 
v_val_4939_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4941_ = v___x_4934_;
v_isShared_4942_ = v_isSharedCheck_4950_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_val_4939_);
lean_dec(v___x_4934_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4950_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4946_; 
v___x_4943_ = lean_array_get_size(v_a_4933_);
v___x_4944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
lean_ctor_set(v___x_4944_, 1, v_val_4939_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 0, v___x_4944_);
v___x_4946_ = v___x_4941_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4944_);
v___x_4946_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
v___x_4948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
lean_ctor_set(v___x_4948_, 1, v___x_4932_);
return v___x_4948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4951_, lean_object* v_as_4952_, lean_object* v_sz_4953_, lean_object* v_i_4954_, lean_object* v_b_4955_){
_start:
{
size_t v_sz_boxed_4956_; size_t v_i_boxed_4957_; lean_object* v_res_4958_; 
v_sz_boxed_4956_ = lean_unbox_usize(v_sz_4953_);
lean_dec(v_sz_4953_);
v_i_boxed_4957_ = lean_unbox_usize(v_i_4954_);
lean_dec(v_i_4954_);
v_res_4958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4951_, v_as_4952_, v_sz_boxed_4956_, v_i_boxed_4957_, v_b_4955_);
lean_dec_ref(v_b_4955_);
lean_dec_ref(v_as_4952_);
lean_dec(v_fnIdx_4951_);
return v_res_4958_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4961_ = l_Lean_stringToMessageData(v___x_4960_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4962_, lean_object* v_positions_4963_, lean_object* v_fnIdx_4964_, lean_object* v_brecOnConst_4965_, lean_object* v_packedFArgs_4966_, lean_object* v_funTypes_4967_, lean_object* v_ys_4968_, lean_object* v___value_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v___x_4989_; lean_object* v_fst_4990_; lean_object* v_snd_4991_; lean_object* v___x_4992_; size_t v_sz_4993_; size_t v___x_4994_; lean_object* v___x_4995_; lean_object* v_fst_4996_; 
lean_inc_ref(v_ys_4968_);
lean_inc_ref(v_recArgInfo_4962_);
v___x_4989_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4962_, v_ys_4968_);
v_fst_4990_ = lean_ctor_get(v___x_4989_, 0);
lean_inc(v_fst_4990_);
v_snd_4991_ = lean_ctor_get(v___x_4989_, 1);
lean_inc(v_snd_4991_);
lean_dec_ref(v___x_4989_);
v___x_4992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_4993_ = lean_array_size(v_positions_4963_);
v___x_4994_ = ((size_t)0ULL);
v___x_4995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4964_, v_positions_4963_, v_sz_4993_, v___x_4994_, v___x_4992_);
v_fst_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_fst_4996_);
lean_dec_ref(v___x_4995_);
if (lean_obj_tag(v_fst_4996_) == 0)
{
lean_dec(v_snd_4991_);
lean_dec(v_fst_4990_);
lean_dec_ref(v_ys_4968_);
lean_dec_ref(v_brecOnConst_4965_);
lean_dec_ref(v_recArgInfo_4962_);
goto v___jp_4975_;
}
else
{
lean_object* v_val_4997_; 
v_val_4997_ = lean_ctor_get(v_fst_4996_, 0);
lean_inc(v_val_4997_);
lean_dec_ref_known(v_fst_4996_, 1);
if (lean_obj_tag(v_val_4997_) == 1)
{
lean_object* v_val_4998_; lean_object* v_fst_4999_; lean_object* v_snd_5000_; lean_object* v_indIdx_5001_; lean_object* v_brecOn_5002_; lean_object* v_brecOn_5003_; lean_object* v_brecOn_5004_; lean_object* v___x_5005_; 
lean_dec(v_fnIdx_4964_);
lean_dec_ref(v_positions_4963_);
v_val_4998_ = lean_ctor_get(v_val_4997_, 0);
lean_inc(v_val_4998_);
lean_dec_ref_known(v_val_4997_, 1);
v_fst_4999_ = lean_ctor_get(v_val_4998_, 0);
lean_inc(v_fst_4999_);
v_snd_5000_ = lean_ctor_get(v_val_4998_, 1);
lean_inc(v_snd_5000_);
lean_dec(v_val_4998_);
v_indIdx_5001_ = lean_ctor_get(v_recArgInfo_4962_, 5);
lean_inc(v_indIdx_5001_);
lean_dec_ref(v_recArgInfo_4962_);
v_brecOn_5002_ = lean_apply_1(v_brecOnConst_4965_, v_indIdx_5001_);
v_brecOn_5003_ = l_Lean_mkAppN(v_brecOn_5002_, v_fst_4990_);
lean_dec(v_fst_4990_);
v_brecOn_5004_ = l_Lean_mkAppN(v_brecOn_5003_, v_packedFArgs_4966_);
v___x_5005_ = l_Lean_Meta_PProdN_projM(v_fst_4999_, v_snd_5000_, v_brecOn_5004_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
lean_dec(v_snd_5000_);
lean_dec(v_fst_4999_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5007_; uint8_t v___x_5008_; uint8_t v___x_5009_; lean_object* v___x_5010_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_a_5006_);
lean_dec_ref_known(v___x_5005_, 1);
v___x_5007_ = l_Lean_mkAppN(v_a_5006_, v_snd_4991_);
lean_dec(v_snd_4991_);
v___x_5008_ = 1;
v___x_5009_ = 1;
v___x_5010_ = l_Lean_Meta_mkLetFVars(v_funTypes_4967_, v___x_5007_, v___x_5008_, v___x_5008_, v___x_5009_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v_a_5011_; uint8_t v___x_5012_; lean_object* v___x_5013_; 
v_a_5011_ = lean_ctor_get(v___x_5010_, 0);
lean_inc(v_a_5011_);
lean_dec_ref_known(v___x_5010_, 1);
v___x_5012_ = 0;
v___x_5013_ = l_Lean_Meta_mkLambdaFVars(v_ys_4968_, v_a_5011_, v___x_5012_, v___x_5008_, v___x_5012_, v___x_5008_, v___x_5009_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
lean_dec_ref(v_ys_4968_);
return v___x_5013_;
}
else
{
lean_dec_ref(v_ys_4968_);
return v___x_5010_;
}
}
else
{
lean_dec(v_snd_4991_);
lean_dec_ref(v_ys_4968_);
return v___x_5005_;
}
}
else
{
lean_dec(v_val_4997_);
lean_dec(v_snd_4991_);
lean_dec(v_fst_4990_);
lean_dec_ref(v_ys_4968_);
lean_dec_ref(v_brecOnConst_4965_);
lean_dec_ref(v_recArgInfo_4962_);
goto v___jp_4975_;
}
}
v___jp_4975_:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4976_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_4977_ = l_Nat_reprFast(v_fnIdx_4964_);
v___x_4978_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
v___x_4979_ = l_Lean_MessageData_ofFormat(v___x_4978_);
v___x_4980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4976_);
lean_ctor_set(v___x_4980_, 1, v___x_4979_);
v___x_4981_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_4982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4980_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
v___x_4983_ = lean_array_to_list(v_positions_4963_);
v___x_4984_ = lean_box(0);
v___x_4985_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_4983_, v___x_4984_);
v___x_4986_ = l_Lean_MessageData_ofList(v___x_4985_);
v___x_4987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4982_);
lean_ctor_set(v___x_4987_, 1, v___x_4986_);
v___x_4988_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4987_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
return v___x_4988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5014_, lean_object* v_positions_5015_, lean_object* v_fnIdx_5016_, lean_object* v_brecOnConst_5017_, lean_object* v_packedFArgs_5018_, lean_object* v_funTypes_5019_, lean_object* v_ys_5020_, lean_object* v___value_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5014_, v_positions_5015_, v_fnIdx_5016_, v_brecOnConst_5017_, v_packedFArgs_5018_, v_funTypes_5019_, v_ys_5020_, v___value_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec_ref(v___value_5021_);
lean_dec_ref(v_funTypes_5019_);
lean_dec_ref(v_packedFArgs_5018_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5028_, lean_object* v_fnIdx_5029_, lean_object* v_brecOnConst_5030_, lean_object* v_packedFArgs_5031_, lean_object* v_funTypes_5032_, lean_object* v_recArgInfo_5033_, lean_object* v_value_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v___f_5040_; uint8_t v___x_5041_; lean_object* v___x_5042_; 
v___f_5040_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5040_, 0, v_recArgInfo_5033_);
lean_closure_set(v___f_5040_, 1, v_positions_5028_);
lean_closure_set(v___f_5040_, 2, v_fnIdx_5029_);
lean_closure_set(v___f_5040_, 3, v_brecOnConst_5030_);
lean_closure_set(v___f_5040_, 4, v_packedFArgs_5031_);
lean_closure_set(v___f_5040_, 5, v_funTypes_5032_);
v___x_5041_ = 0;
v___x_5042_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5034_, v___f_5040_, v___x_5041_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5043_, lean_object* v_fnIdx_5044_, lean_object* v_brecOnConst_5045_, lean_object* v_packedFArgs_5046_, lean_object* v_funTypes_5047_, lean_object* v_recArgInfo_5048_, lean_object* v_value_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5043_, v_fnIdx_5044_, v_brecOnConst_5045_, v_packedFArgs_5046_, v_funTypes_5047_, v_recArgInfo_5048_, v_value_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_);
lean_dec(v_a_5053_);
lean_dec_ref(v_a_5052_);
lean_dec(v_a_5051_);
lean_dec_ref(v_a_5050_);
return v_res_5055_;
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
